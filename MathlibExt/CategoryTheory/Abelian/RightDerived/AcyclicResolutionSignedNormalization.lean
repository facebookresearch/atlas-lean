/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.AcyclicResolutionSignedCorrection
public import MathlibExt.CategoryTheory.Abelian.RightDerived.OpResolutionNormalization
public import MathlibExt.CategoryTheory.Abelian.RightDerived.AcyclicResolution

/-!
# Triangular signs in the injective acyclic comparison

For an additive left-exact functor between abelian categories, the
acyclic-resolution comparison on an injective resolution differs from
its canonical right-derived comparison by the sign
`σ_n=(-1)^(n(n+1)/2)`. Injective terms have the required vanishing of
positive right-derived values.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace CategoryTheory
/-- In a preadditive category `E`, let `a : X₀ → X₁`,
`b : X₁ ≅ X₂`, `c : X₂ ≅ X₃`, and `s ∈ ℤ`.
Then `(a ≫ b ≫ c) ≫ (s • (c⁻¹ ≫ b⁻¹)) = s • a`. -/
theorem normalizationIsoPair_zsmul_cancel {E : Type u} [Category.{v} E] [Preadditive E]
    {X₀ X₁ X₂ X₃ : E} (a : X₀ ⟶ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃) (s : ℤ) :
    (a ≫ b.hom ≫ c.hom) ≫ (s • (c.inv ≫ b.inv)) = s • a := by
  rw [comp_zsmul]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
end CategoryTheory

namespace CategoryTheory.InjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive. For every injective resolution `J` of `X`,
all its terms are `F`-acyclic: `R^(n+1)F(J^q)=0` for every `q,n`. -/
theorem normalizationInjectiveTerms_acyclic {X : C} (J : InjectiveResolution X)
    (F : C ⥤ D) [F.Additive] :
    ∀ q n : ℕ, IsZero ((F.rightDerived (n + 1)).obj (J.cocomplex.X q)) :=
  fun q n => F.isZero_rightDerived_obj_injective_succ n (J.cocomplex.X q)

set_option backward.isDefEq.respectTransparency false in
/-- Let `C,D` be abelian, with injective resolutions in `C`,
`F : C → D` additive and preserving finite limits, and `J` an
injective resolution of `X` with `R^(i+1)F(J^q)=0` for every `q,i`. In degree `n`, the forward acyclic comparison on `J` is
`σ_n` times the forward canonical injective-resolution comparison,
where `σ_n` is the triangular normalization sign. -/
theorem normalizationAcyclicInjective_hom {X : C} (J : InjectiveResolution X)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (hJ : ∀ q i : ℕ, IsZero ((F.rightDerived (i + 1)).obj (J.cocomplex.X q))) (n : ℕ) :
    (F.rightDerivedObjIsoHomologyOfAcyclicResolution J.cocomplex J.ι hJ n).hom =
      ProjectiveResolution.acyclicResolutionNormalizationSign n •
          (J.isoRightDerivedObj F n).hom := by
  let : HasProjectiveResolutions Cᵒᵖ :=
    { out Y := ⟨⟨injectiveResolutionOpProj (injectiveResolution Y.unop)⟩⟩ }
  let : PreservesFiniteColimits F.op := preservesFiniteColimits_op F
  let P := injectiveResolutionOpProj J
  let hP := ProjectiveResolution.normalizationProjectiveTerms_acyclic P F.op
  let eL := F.op.leftDerivedObjIsoHomologyOfAcyclicResolution P.complex P.π hP n
  let K : CochainComplex D ℕ := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
  let q : (F.op.leftDerived n).obj (Opposite.op X) ≅ Opposite.op (K.homology n) :=
    eL ≪≫ K.homologyOp n
  let b := (K.homologyOp n).unop
  let c := (P.isoLeftDerivedObj F.op n).unop
  let a := (J.isoRightDerivedObj F n).hom
  let s := ProjectiveResolution.acyclicResolutionNormalizationSign n
  have heR : (F.rightDerivedObjIsoHomologyOfAcyclicResolution J.cocomplex J.ι hJ n).hom =
      ((F.rightDerivedOpIso n).app X).hom ≫ q.inv.unop := by
    change ((F.rightDerivedOpIso n).app X).hom ≫
      (((K.homologyOp n).inv ≫
        ((HomologicalComplex.homologyFunctor Dᵒᵖ (ComplexShape.down ℕ) n).map
          (𝟙 ((F.op.mapHomologicalComplex (ComplexShape.down ℕ)).obj J.cocomplex.op)))) ≫
            eL.inv).unop = _
    let Z := (F.op.mapHomologicalComplex (ComplexShape.down ℕ)).obj J.cocomplex.op
    let H := HomologicalComplex.homologyFunctor Dᵒᵖ (ComplexShape.down ℕ) n
    have hid : H.map (𝟙 Z) = 𝟙 (H.obj Z) := H.map_id Z
    exact (congrArg (fun t => ((F.rightDerivedOpIso n).app X).hom ≫
      (((K.homologyOp n).inv ≫ t) ≫ eL.inv).unop) hid).trans
      (congrArg (fun t => ((F.rightDerivedOpIso n).app X).hom ≫
        (t ≫ eL.inv).unop) (Category.comp_id (K.homologyOp n).inv))
  have heOp : ((F.rightDerivedOpIso n).app X).hom = a ≫ b.hom ≫ c.hom :=
    Functor.rightDerivedOpIsoApp_hom_ofInjectiveResolution J F n
  have hl : eL.inv = s • (P.isoLeftDerivedObj F.op n).inv :=
    ProjectiveResolution.normalizationAcyclicProjective_inv P F.op hP n
  have hq : q.inv.unop = s • (c.inv ≫ b.inv) := by
    dsimp only [q, Iso.trans_inv]
    rw [hl]
    simp only [unop_comp, unop_zsmul, zsmul_comp]
    rfl
  calc
    (F.rightDerivedObjIsoHomologyOfAcyclicResolution J.cocomplex J.ι hJ n).hom =
        ((F.rightDerivedOpIso n).app X).hom ≫ q.inv.unop := heR
    _ = (a ≫ b.hom ≫ c.hom) ≫ q.inv.unop :=
      congrArg (fun t => t ≫ q.inv.unop) heOp
    _ = (a ≫ b.hom ≫ c.hom) ≫ (s • (c.inv ≫ b.inv)) :=
      congrArg (fun t => (a ≫ b.hom ≫ c.hom) ≫ t) hq
    _ = s • a := normalizationIsoPair_zsmul_cancel a b c s

set_option backward.isDefEq.respectTransparency false in
/-- Let `C,D` be abelian, with injective resolutions in `C`,
`F : C → D` additive and preserving finite limits, and `J` an
injective resolution of `X` with `R^(i+1)F(J^q)=0` for every `q,i`. The forward acyclic comparison equals
`(-1)^(n(n+1)/2)` times the canonical map
`R^nF(X) → Hⁿ(F(J))`. -/
theorem normalizationAcyclicInjective_hom_closed {X : C} (J : InjectiveResolution X)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (hJ : ∀ q i : ℕ, IsZero ((F.rightDerived (i + 1)).obj (J.cocomplex.X q))) (n : ℕ) :
    (F.rightDerivedObjIsoHomologyOfAcyclicResolution J.cocomplex J.ι hJ n).hom =
      ((-1 : ℤ) ^ (n * (n + 1) / 2)) • (J.isoRightDerivedObj F n).hom := by
  rw
      [normalizationAcyclicInjective_hom,
        ProjectiveResolution.acyclicResolutionNormalizationSign_closed]

end CategoryTheory.InjectiveResolution
