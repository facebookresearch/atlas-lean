/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.Projective.KernelTailSignedHorseshoe
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.HorseshoeBoundaryChoice
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology

/-!
# Higher kernel-tail boundaries and their alternating coefficient

For a projective resolution `P` in an abelian category, let `T` be
its kernel-tail resolution. An additive functor gives
`H_(n+1)(F(T)) ≅ H_(n+2)(F(P))`. The signed horseshoe boundary
followed by this isomorphism is `(-1)^(n+2)` times the identity.
The same formula holds for the canonical derived boundary under
the endpoint resolution comparisons.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]


set_option backward.isDefEq.respectTransparency false in
/-- Let `C,D` be abelian, `F : C → D` additive, and `Q` a
nonnegative chain complex. For kernel-tail indices `j=i+1`, applying
`F` to the coordinate isomorphism of the restricted term `Q_j`
gives the coordinate isomorphism for the restriction of `F(Q)`. -/
theorem normalizationRestrictionXIso_map_hom (F : C ⥤ D) [F.Additive]
    (Q : ChainComplex C ℕ) {i j : ℕ} (h : ChainComplex.kernelTailEmbedding.f i = j) :
    F.map (Q.restrictionXIso ChainComplex.kernelTailEmbedding h).hom =
      (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).restrictionXIso
        ChainComplex.kernelTailEmbedding h).hom := by
  subst h
  simp [HomologicalComplex.restrictionXIso]

/-- Let `C,D` be abelian, `F : C → D` additive, and take maps
`d_L : L₁ → L₀`, `b : R₁ → L₀`, `d_R : R₁ → R₀`.
For `x : A → F(R₁)` with `x ≫ F(d_R)=0`, inserting `x` by the
right inclusion then applying the mapped block differential gives
`x ≫ F(b)` inserted by the left inclusion in `F(L₀ ⊞ R₀)`. -/
theorem normalizationMappedBiprod_inr_boundary (F : C ⥤ D) [F.Additive]
    {L₁ L₀ R₁ R₀ : C} (dL : L₁ ⟶ L₀) (b : R₁ ⟶ L₀) (dR : R₁ ⟶ R₀)
    {A : D} (x : A ⟶ F.obj R₁) (hx : x ≫ F.map dR = 0) :
    x ≫ F.map (biprod.inr : R₁ ⟶ L₁ ⊞ R₁) ≫
      F.map (Biprod.ofComponents dL 0 b dR) =
        x ≫ F.map b ≫ F.map (biprod.inl : L₀ ⟶ L₀ ⊞ R₀) := by
  rw [← F.map_comp, Biprod.inr_ofComponents, F.map_add, F.map_comp, F.map_comp]
  simp only [comp_add, ← Category.assoc, hx, zero_comp, add_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Let `C,D` be abelian, `P` a projective resolution of `X`,
`T` its kernel-tail resolution of `ker(P₀ → X)`, and `F : C → D` additive. Restriction gives a canonical homology isomorphism
`H_(n+1)(F(T)) ≅ H_(n+2)(F(P))` for each `n ∈ ℕ`. -/
def normalizationKernelTailHomologyIso {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (normalizationKernelTail P).complex).homology (n + 1) ≅
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology (n + 2) := by
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  change (K.restriction ChainComplex.kernelTailEmbedding).homology (n + 1) ≅ K.homology (n + 2)
  exact K.restrictionHomologyIso ChainComplex.kernelTailEmbedding (n + 2) (n + 1) n
    (by simp) (by simp) (i' := n + 3) (j' := n + 2) (k' := n + 1)
    rfl rfl rfl (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- Let `C,D` be abelian, `P` a projective resolution of `X`,
`T` its kernel-tail resolution of `ker(P₀ → X)`, and `F : C → D` additive. The mapped signed-horseshoe boundary
`H_(n+2)(F(P)) → H_(n+1)(F(T))`, followed by the restriction
isomorphism, is `(-1)^(n+2) • 𝟙` on `H_(n+2)(F(P))`. -/
theorem normalizationKernelTail_mappedBoundary_sign {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    ((normalizationKernelTailHorseshoe P).mapped_shortExact
      (normalizationKernelTailHorseshoeSpec P) F).δ (n + 2) (n + 1) rfl ≫
        (normalizationKernelTailHomologyIso P F n).hom =
      normalizationCrossSign (n + 1) • 𝟙
        (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology (n + 2)) := by
  let H := normalizationKernelTailHorseshoe P
  let sp := normalizationKernelTailHorseshoeSpec P
  let R := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let L := R.restriction ChainComplex.kernelTailEmbedding
  let T := H.mapped F
  let M := T.X₂
  let hT := H.mapped_shortExact sp F
  let x : R.cycles (n + 2) ⟶ F.obj (P.complex.X (n + 2)) := R.iCycles (n + 2)
  let x₂ := x ≫ F.map (biprod.inr :
    P.complex.X (n + 2) ⟶ (normalizationMiddleComplex P).X (n + 2))
  let y := normalizationCrossSign (n + 1) •
    (x ≫ F.map (normalizationKernelTailXIso P (n + 1)).inv)
  have hx : x ≫ R.d (n + 2) (n + 1) = 0 := R.iCycles_d _ _
  have hx₂ : x₂ ≫ T.g.f (n + 2) = x := by
    change (x ≫ F.map biprod.inr) ≫ F.map biprod.snd = x
    rw [Category.assoc, ← F.map_comp, biprod.inr_snd, F.map_id]
    exact Category.comp_id x
  have hy : y ≫ T.f.f (n + 1) = x₂ ≫ M.d (n + 2) (n + 1) := by
    change y ≫ F.map biprod.inl =
      (x ≫ F.map biprod.inr) ≫ F.map ((normalizationMiddleComplex P).d (n + 2) (n + 1))
    rw [normalizationMiddleComplex_d]
    have hb := normalizationMappedBiprod_inr_boundary F
      ((normalizationKernelTail P).complex.d (n + 2) (n + 1))
      (normalizationCross P (n + 1)) (P.complex.d (n + 2) (n + 1)) x hx
    dsimp only [normalizationMiddleDifferential]
    rw [Category.assoc, hb]
    simp only [normalizationCross, Functor.map_zsmul, comp_zsmul, y, zsmul_comp,
      Category.assoc]
  have hyL : y ≫ L.d (n + 1) n = 0 := by
    have := hT.mono_f
    change y ≫ T.X₁.d (n + 1) n = 0
    apply (cancel_mono (T.f.f n)).1
    rw [zero_comp, Category.assoc, ← T.f.comm, ← Category.assoc, hy]
    rw [Category.assoc, M.d_comp_d, comp_zero]
  have hδ := hT.δ_eq (n + 2) (n + 1) rfl x hx x₂ hx₂ y hy n (by simp)
  have h := congrArg (fun q => q ≫ (normalizationKernelTailHomologyIso P F n).hom) hδ
  have hxid : R.liftCycles x (n + 1) (by simp) hx = 𝟙 (R.cycles (n + 2)) := by
    apply (cancel_mono (R.iCycles (n + 2))).1
    simp only [HomologicalComplex.liftCycles_i, Category.id_comp]
    rfl
  let ec := R.restrictionCyclesIso ChainComplex.kernelTailEmbedding (n + 1) n
    (by simp) (j' := n + 2) (k' := n + 1) rfl rfl (by simp)
  have he : F.map (normalizationKernelTailXIso P (n + 1)).inv ≫
      (R.restrictionXIso ChainComplex.kernelTailEmbedding (show
        ChainComplex.kernelTailEmbedding.f (n + 1) = n + 2 from rfl)).hom =
        𝟙 (R.X (n + 2)) := by
    dsimp only [normalizationKernelTailXIso]
    rw [← normalizationRestrictionXIso_map_hom F P.complex]
    rw [← F.map_comp, Iso.inv_hom_id, F.map_id]
    rfl
  have hyid : L.liftCycles y n (by simp) hyL ≫ ec.hom =
      normalizationCrossSign (n + 1) • 𝟙 (R.cycles (n + 2)) := by
    apply (cancel_mono (R.iCycles (n + 2))).1
    dsimp only [ec]
    rw [Category.assoc, HomologicalComplex.restrictionCyclesIso_hom_iCycles]
    rw [← Category.assoc, HomologicalComplex.liftCycles_i]
    dsimp only [y]
    simp only [zsmul_comp, Category.assoc, he, Category.id_comp]
    exact congrArg (fun q => normalizationCrossSign (n + 1) • q) (Category.comp_id x)
  have hp : L.homologyπ (n + 1) ≫ (normalizationKernelTailHomologyIso P F n).hom =
      ec.hom ≫ R.homologyπ (n + 2) := by
    exact R.homologyπ_restrictionHomologyIso_hom ChainComplex.kernelTailEmbedding
      (n + 2) (n + 1) n (by simp) (by simp) rfl rfl rfl (by simp) (by simp)
  change (R.liftCycles x (n + 1) (by simp) hx ≫ R.homologyπ (n + 2) ≫
      hT.δ (n + 2) (n + 1) rfl) ≫ (normalizationKernelTailHomologyIso P F n).hom =
    (L.liftCycles y n (by simp) hyL ≫ L.homologyπ (n + 1)) ≫
      (normalizationKernelTailHomologyIso P F n).hom at h
  rw [hxid, Category.id_comp] at h
  simp only [Category.assoc] at h
  rw [hp] at h
  simp only [← Category.assoc] at h
  rw [hyid] at h
  change hT.δ (n + 2) (n + 1) rfl ≫ (normalizationKernelTailHomologyIso P F n).hom =
    normalizationCrossSign (n + 1) • 𝟙 (R.homology (n + 2))
  apply (cancel_epi (R.homologyπ (n + 2))).1
  simpa only [Category.assoc, zsmul_comp, comp_zsmul, Category.id_comp, Category.comp_id] using h

variable [HasProjectiveResolutions C]

set_option backward.isDefEq.respectTransparency false in
/-- Let `C,D` be abelian, `P` a projective resolution of `X`,
`T` its kernel-tail resolution of `ker(P₀ → X)`, and `F : C → D` additive. Suppose `C` has projective resolutions. The canonical boundary
`L_(n+2)F(X) → L_(n+1)F(ker(P₀ → X))`, conjugated by the
resolution comparisons and followed by the tail restriction
isomorphism, is `(-1)^(n+2) • 𝟙` on `H_(n+2)(F(P))`. -/
theorem normalizationKernelTail_nativeBoundary_sign {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (P.isoLeftDerivedObj F (n + 2)).inv ≫
      LeftDerivedDelta.LDdelta F (n + 1) (ShortComplex.kernelSequence (P.π.f 0))
        (normalizationKernelSequence_shortExact P) ≫
      ((normalizationKernelTail P).isoLeftDerivedObj F (n + 1)).hom ≫
      (normalizationKernelTailHomologyIso P F n).hom =
        normalizationCrossSign (n + 1) • 𝟙
          (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology (n + 2)) := by
  rw [← (normalizationKernelTailHorseshoe P).delta_eq_native
    (normalizationKernelTailHorseshoeSpec P) F (n + 1)]
  dsimp only [HorseshoeData.delta, normalizationKernelTailHorseshoe,
    ShortComplex.kernelSequence]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (Iso.inv_hom_id_assoc (P.isoLeftDerivedObj F (n + 2)) _).trans
    (normalizationKernelTail_mappedBoundary_sign P F n)

end CategoryTheory.ProjectiveResolution
