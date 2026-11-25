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
  (smallEtaleConnectingMap.{u, w} hS 0).comp
    (smallEtaleH0Sections.{u, w} X S.X₃).symm.toAddMonoidHom


-- Keep the finite increase local while retaining the actual Ext zero-composite.
/-- Zero boundary is equivalent to an actual original global section lift. -/
theorem smallEtaleSectionBoundary_zero_iff (hS : S.ShortExact)
    (c : S.X₃.obj.obj (op (Scheme.Etale.mk (𝟙 X)))) :
    smallEtaleSectionBoundary.{u, w} hS c = 0 ↔
      ∃ b : S.X₂.obj.obj (op (Scheme.Etale.mk (𝟙 X))),
        S.g.hom.app (op (Scheme.Etale.mk (𝟙 X))) b = c := by
  constructor
  · intro hc
    exact Sheaf.H.longSequence_equiv₀_exact₃ (hS := hS)
      (hT := identityEtaleIsTerminal X) c hc
  · rintro ⟨b, hb⟩
    let x := (smallEtaleH0Sections.{u, w} X S.X₂).symm b
    have hz : smallEtaleConnectingMap.{u, w} hS 0 (Sheaf.H.map S.g 0 x) = 0 := by
      change (x.comp (Ext.mk₀ S.g) (add_zero 0)).comp hS.extClass rfl = 0
      simp only [Ext.comp_assoc_of_second_deg_zero,
        ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
    have hx : Sheaf.H.map S.g 0 x = (smallEtaleH0Sections.{u, w} X S.X₃).symm c := by
      change Sheaf.H.map S.g 0 ((Sheaf.H.equiv₀ S.X₂ (identityEtaleIsTerminal X)).symm b) =
        (Sheaf.H.equiv₀ S.X₃ (identityEtaleIsTerminal X)).symm c
      rw [Sheaf.H.equiv₀_symm_naturality (f := S.g) (hT := identityEtaleIsTerminal X) b, hb]
    change smallEtaleConnectingMap.{u, w} hS 0 (Sheaf.H.map S.g 0 x) = 0 at hz
    rw [hx] at hz
    exact hz

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
