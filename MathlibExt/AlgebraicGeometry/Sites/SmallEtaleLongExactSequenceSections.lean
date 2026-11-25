/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleLongExactSequence

/-!
# Sections in étale long exact sequences
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

variable (X : Scheme.{u})

/-- The actual canonical degree-zero evaluation at the original identity object. -/
def smallEtaleH0Sections (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    Sheaf.H Q 0 ≃+ Q.obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
  Sheaf.H.equiv₀ Q (identityEtaleIsTerminal X)

/-- This is exactly A's original integral-generator identification. -/
theorem smallEtaleH0Sections_eq_integralHomTerminal
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (x : Sheaf.H Q 0) :
    smallEtaleH0Sections.{u, w} X Q x =
      integralHomTerminal.{u, w} X Q (Ext.addEquiv₀ x) := rfl

/-- Both original sequence arrows are carried to their literal section components. -/
theorem smallEtaleH0Sections_naturality
    {Q R : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}
    (τ : Q ⟶ R) (x : Sheaf.H Q 0) :
    smallEtaleH0Sections.{u, w} X R (Sheaf.H.map τ 0 x) =
      τ.hom.app (op (Scheme.Etale.mk (𝟙 X))) (smallEtaleH0Sections.{u, w} X Q x) :=
  (Sheaf.H.equiv₀_naturality (f := τ) (hT := identityEtaleIsTerminal X) x).symm

variable {X}
  {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})}



/-- The boundary of an actual original global section, using the same δ of S. -/
def smallEtaleSectionBoundary (hS : S.ShortExact) :
    S.X₃.obj.obj (op (Scheme.Etale.mk (𝟙 X))) →+ Sheaf.H S.X₁ 1 :=
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}
  let A := AddCommGrpCat.{max u w}
  let _ : HasExt.{max u w} C := smallEtaleHasExt.{u, w} X
  let H₀ : C ⥤ A := Sheaf.H.functorH.{max u w, max u w, u, u + 1} X.smallEtaleTopology 0
  let H₁ : C ⥤ A := Sheaf.H.functorH.{max u w, max u w, u, u + 1} X.smallEtaleTopology 1
  let e : H₀.obj S.X₃ ≅ S.X₃.obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
    (smallEtaleH0Sections.{u, w} X S.X₃).toAddCommGrpIso
  let δ : H₀.obj S.X₃ ⟶ H₁.obj S.X₁ :=
    AddCommGrpCat.ofHom (X := H₀.obj S.X₃) (Y := H₁.obj S.X₁)
      (smallEtaleConnectingMap.{u, w} (X := X) (S := S) hS 0)
  (e.inv ≫ δ).hom


/-- Zero boundary is equivalent to an actual original global section lift. -/
theorem smallEtaleSectionBoundary_zero_iff (hS : S.ShortExact)
    (c : S.X₃.obj.obj (op (Scheme.Etale.mk (𝟙 X)))) :
    smallEtaleSectionBoundary.{u, w} hS c = 0 ↔
      ∃ b : S.X₂.obj.obj (op (Scheme.Etale.mk (𝟙 X))),
        S.g.hom.app (op (Scheme.Etale.mk (𝟙 X))) b = c := by
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}
  let A := AddCommGrpCat.{max u w}
  let _ : HasExt.{max u w} C := smallEtaleHasExt.{u, w} X
  let H₀ : C ⥤ A := Sheaf.H.functorH.{max u w, max u w, u, u + 1} X.smallEtaleTopology 0
  let H₁ : C ⥤ A := Sheaf.H.functorH.{max u w, max u w, u, u + 1} X.smallEtaleTopology 1
  let e₂ : Sheaf.H S.X₂ 0 ≃+ S.X₂.obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
    smallEtaleH0Sections.{u, w} X S.X₂
  let e₃ : Sheaf.H S.X₃ 0 ≃+ S.X₃.obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
    smallEtaleH0Sections.{u, w} X S.X₃
  let g : H₀.obj S.X₂ ⟶ H₀.obj S.X₃ := H₀.map S.g
  let δ : H₀.obj S.X₃ ⟶ H₁.obj S.X₁ :=
    AddCommGrpCat.ofHom (X := H₀.obj S.X₃) (Y := H₁.obj S.X₁)
      (smallEtaleConnectingMap.{u, w} (X := X) (S := S) hS 0)
  constructor
  · intro hc
    have hδ : δ.hom (e₃.symm c) = 0 := hc
    exact Sheaf.H.longSequence_equiv₀_exact₃ (hS := hS)
      (hT := identityEtaleIsTerminal X) c hδ
  · rintro ⟨b, hb⟩
    let x : H₀.obj S.X₂ := e₂.symm b
    have hZero : g ≫ δ = 0 :=
      (Sheaf.H.longSequence_exact hS 0 1 rfl).zero 1
    have hδ : δ.hom (g.hom x) = 0 := ConcreteCategory.congr_hom hZero x
    have hg : g.hom x = e₃.symm c :=
      (Sheaf.H.equiv₀_symm_naturality (f := S.g)
        (hT := identityEtaleIsTerminal X) b).trans (congrArg e₃.symm hb)
    exact (congrArg δ.hom hg).symm.trans hδ

/-- The actual first original global-section map is injective. -/
theorem smallEtaleFirstSectionMap_injective (hS : S.ShortExact) :
    Function.Injective (S.f.hom.app (op (Scheme.Etale.mk (𝟙 X)))) := by
  intro a b hab
  apply (smallEtaleH0Sections.{u, w} X S.X₁).symm.injective
  apply smallEtaleLongSequence_initial_injective hS
  change Sheaf.H.map S.f 0 ((Sheaf.H.equiv₀ S.X₁ (identityEtaleIsTerminal X)).symm a) =
    Sheaf.H.map S.f 0 ((Sheaf.H.equiv₀ S.X₁ (identityEtaleIsTerminal X)).symm b)
  rw [Sheaf.H.equiv₀_symm_naturality (f := S.f) (hT := identityEtaleIsTerminal X) a,
    Sheaf.H.equiv₀_symm_naturality (f := S.f) (hT := identityEtaleIsTerminal X) b, hab]

end AlgebraicGeometry.Scheme.DerivedSections
