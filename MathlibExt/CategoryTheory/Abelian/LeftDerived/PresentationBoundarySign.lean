/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Abelian.Projective.PresentationHorseshoeSpec
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.HorseshoeBoundaryChoice

/-!
# Degree-one sign of a projective presentation boundary

Let `A → B → X` be short exact in an abelian category with projective
resolutions, with `A,B` projective. For an additive functor `F`, a
map into `F(A)` killed by `F(A → B)` represents a degree-one class
of the quotient presentation. Its left-derived boundary followed
by `L₀F(A) → F(A)` is the negative original map, because the
middle presentation differential has left coordinate `-id`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (S : ShortComplex C) (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂]
variable (F : C ⥤ D) [F.Additive]

set_option backward.isDefEq.respectTransparency false in
/-- Let `C,D` be abelian, with projective resolutions in `C`,
`S : A → B → X` short exact with `A,B` projective, and `F : C → D`
additive. For `x : Z → F(A)` with `x ≫ F(S.f)=0`, its class in
`H₁(F(A → B))`, compared to `L₁F(X)`, then mapped by the boundary
to `L₀F(A)` and the canonical augmentation to `F(A)`, is `-x`. -/
theorem presentationBoundary_cycle_sign {A : D} (x : A ⟶ F.obj S.X₁)
    (hx : x ≫ F.map S.f = 0) :
    let R := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (ofPresentation S hS).complex
    R.liftCycles x 0 (by simp) (by
      change x ≫ F.map ((ofPresentation S hS).complex.d 1 0) = 0
      exact (congrArg (fun q : S.X₁ ⟶ S.X₂ => x ≫ F.map q)
        (presentationComplex_d_zero S)).trans hx) ≫ R.homologyπ 1 ≫
      ((ofPresentation S hS).isoLeftDerivedObj F 1).inv ≫
      LeftDerivedDelta.LDdelta F 0 S hS ≫ F.fromLeftDerivedZero.app S.X₁ = -x := by
  let H := presentationHorseshoe S hS
  let sp := presentationHorseshoeSpec S hS
  let R := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (ofPresentation S hS).complex
  let L := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (presentationLeftResolution S).complex
  let M := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (presentationMiddleResolution S).complex
  let T := H.mapped F
  let hT := H.mapped_shortExact sp F
  have hxR : x ≫ R.d 1 0 = 0 := by
    change x ≫ F.map ((ofPresentation S hS).complex.d 1 0) = 0
    exact (congrArg (fun q : S.X₁ ⟶ S.X₂ => x ≫ F.map q)
      (presentationComplex_d_zero S)).trans hx
  have h₂ : x ≫ T.g.f 1 = x := by
    change x ≫ F.map ((presentationHorseshoeProjection S hS).f 1) = x
    rw [presentationHorseshoeProjection_f_one, F.map_id, Category.comp_id]
  have h₁ : (-x) ≫ T.f.f 0 = x ≫ M.d 1 0 := by
    change (-x) ≫ F.map ((presentationHorseshoeInclusion S).f 0) =
      x ≫ F.map ((presentationMiddleResolution S).complex.d 1 0)
    have hi := presentationHorseshoeInclusion_f_zero S
    have hd : (presentationMiddleResolution S).complex.d 1 0 =
      (biprod.lift (-𝟙 S.X₁) S.f) := presentationComplex_d_zero (presentationMiddleRow S)
    have hb : (-x) ≫ F.map (biprod.inl : S.X₁ ⟶ S.X₁ ⊞ S.X₂) =
        x ≫ F.map (biprod.lift (-𝟙 S.X₁) S.f) := by
      have hsplit : (biprod.lift (-𝟙 S.X₁) S.f : S.X₁ ⟶ S.X₁ ⊞ S.X₂) =
          (-𝟙 S.X₁) ≫ biprod.inl + S.f ≫ biprod.inr := by
        apply biprod.hom_ext
        · simp only [add_comp, Category.assoc, biprod.inl_fst, biprod.inr_fst,
            Category.comp_id, comp_zero, add_zero, biprod.lift_fst]
        · simp only [add_comp, Category.assoc, biprod.inl_snd, biprod.inr_snd,
            Category.comp_id, comp_zero, zero_add, biprod.lift_snd]
      simp only [hsplit, F.map_add, F.map_comp, F.map_neg,
        comp_add, neg_comp, comp_neg, Category.id_comp, ← Category.assoc,
        hx, zero_comp, add_zero]
    exact (congrArg (fun q : S.X₁ ⟶ S.X₁ ⊞ S.X₂ => (-x) ≫ F.map q) hi).trans
      (hb.trans (congrArg (fun q : S.X₁ ⟶ S.X₁ ⊞ S.X₂ => x ≫ F.map q) hd.symm))
  have hδ := hT.δ_eq 1 0 (by rfl) x hxR x h₂ (-x) h₁ 0 (by simp)
  have h := congrArg (fun q => q ≫ L.homologyι 0 ≫
    (presentationLeftResolution S).fromLeftDerivedZero' F) hδ
  have hleft :
      ((presentationLeftResolution S).isoLeftDerivedObj F 0).inv ≫
        F.fromLeftDerivedZero.app S.X₁ = L.homologyι 0 ≫
          (presentationLeftResolution S).fromLeftDerivedZero' F := by
    rw [(presentationLeftResolution S).fromLeftDerivedZero_eq F]
    simp only [Iso.inv_hom_id_assoc]
    rfl
  change (R.liftCycles x 0 (by simp) hxR ≫ R.homologyπ 1 ≫ hT.δ 1 0 (by rfl)) ≫
    L.homologyι 0 ≫ (presentationLeftResolution S).fromLeftDerivedZero' F =
    (L.liftCycles (-x) 0 (by simp) _ ≫ L.homologyπ 0) ≫ L.homologyι 0 ≫
      (presentationLeftResolution S).fromLeftDerivedZero' F at h
  simp only [Category.assoc, HomologicalComplex.homology_π_ι_assoc,
    HomologicalComplex.liftCycles_i_assoc] at h
  have hp : L.pOpcycles 0 ≫ (presentationLeftResolution S).fromLeftDerivedZero' F =
      𝟙 (F.obj S.X₁) := by
    exact (pOpcycles_comp_fromLeftDerivedZero' (presentationLeftResolution S) F).trans
      (F.map_id S.X₁)
  have he : (-x) ≫ L.pOpcycles 0 ≫ (presentationLeftResolution S).fromLeftDerivedZero' F = -x :=
    (congrArg (fun q => (-x) ≫ q) hp).trans (Category.comp_id (-x))
  have hfinal := h.trans he
  have hn := H.delta_eq_native sp F 0
  rw [← hn]
  change R.liftCycles x 0 (by simp) hxR ≫ R.homologyπ 1 ≫
    ((ofPresentation S hS).isoLeftDerivedObj F 1).inv ≫
    (((ofPresentation S hS).isoLeftDerivedObj F 1).hom ≫
      hT.δ 1 0 (by rfl) ≫ ((presentationLeftResolution S).isoLeftDerivedObj F 0).inv) ≫
    F.fromLeftDerivedZero.app S.X₁ = -x
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (congrArg (fun q => R.liftCycles x 0 (by simp) hxR ≫
      R.homologyπ 1 ≫ hT.δ 1 0 (by rfl) ≫ q) hleft).trans hfinal

end CategoryTheory.ProjectiveResolution
