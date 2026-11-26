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
# Section boundaries in small étale cohomology

Degree-zero cohomology identifies with sections on the identity étale object. For a short
exact sheaf sequence, use this coordinate to define the section boundary from the last sheaf's
global sections to degree-one cohomology of the first sheaf.

A section has zero boundary precisely when it is the image of a global section of the middle
sheaf. The first sheaf's section map is injective, and the degree-zero section coordinate is
natural in sheaf maps.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

variable (X : Scheme.{u})

/-- Degree zero cohomology as terminal sections.

The group `H⁰(X,Q)` is additively equivalent to sections of `Q` over the identity étale
object. -/
def smallEtaleH0Sections (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    Sheaf.H Q 0 ≃+ Q.obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
  Sheaf.H.equiv₀ Q (identityEtaleIsTerminal X)

/-- Degree zero section coordinate is evaluation of the integral sheaf map.

Under the Ext-zero-to-Hom equivalence, the terminal-section coordinate equals evaluation of
the corresponding integral-sheaf morphism. -/
theorem smallEtaleH0Sections_eq_integralHomTerminal
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (x : Sheaf.H Q 0) :
    smallEtaleH0Sections.{u, w} X Q x =
      integralHomTerminal.{u, w} X Q (Ext.addEquiv₀ x) := rfl

/-- Degree zero section coordinate is natural in sheaf maps.

The cohomology map followed by the target terminal-section coordinate equals the source
coordinate followed by the sheaf map's terminal component. -/
theorem smallEtaleH0Sections_naturality
    {Q R : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}
    (τ : Q ⟶ R) (x : Sheaf.H Q 0) :
    smallEtaleH0Sections.{u, w} X R (Sheaf.H.map τ 0 x) =
      τ.hom.app (op (Scheme.Etale.mk (𝟙 X))) (smallEtaleH0Sections.{u, w} X Q x) :=
  (Sheaf.H.equiv₀_naturality (f := τ) (hT := identityEtaleIsTerminal X) x).symm

variable {X}
  {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})}



/-- Boundary of a global section in degree one cohomology.

Use the inverse degree-zero section equivalence followed by the connecting map to send
sections of the quotient sheaf to `H¹` of the kernel sheaf. -/
def smallEtaleSectionBoundary (hS : S.ShortExact) :
    S.X₃.obj.obj (op (Scheme.Etale.mk (𝟙 X))) →+ Sheaf.H S.X₁ 1 :=
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}
  letI : HasExt.{max u w} C := smallEtaleHasExt.{u, w} X
  (smallEtaleConnectingMap.{u, w} (X := X) (S := S) hS 0).comp
    (smallEtaleH0Sections.{u, w} X S.X₃).symm.toAddMonoidHom


section GenericSections

universe c v s e

private theorem addCommGrp_comp_zero_apply
    {A B D : AddCommGrpCat.{e}} (g : A ⟶ B) (δ : B ⟶ D)
    (h : g ≫ δ = 0) (x : A) : δ.hom (g.hom x) = 0 := by
  have h₀ := congrArg (fun f : A ⟶ D => f.hom x) h
  simpa only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply,
    AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply] using h₀

private theorem sectionBoundary_zero_iff_atTerminal
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{s}] [HasExt.{e} (Sheaf J AddCommGrpCat.{s})]
    {S : ShortComplex (Sheaf J AddCommGrpCat.{s})} (hS : S.ShortExact)
    {T : C} (hT : IsTerminal T) (c : S.X₃.obj.obj (op T)) :
    ((Sheaf.H.δ hS 0 1 rfl).comp (Sheaf.H.equiv₀ S.X₃ hT).symm.toAddMonoidHom) c = 0 ↔
      ∃ b : S.X₂.obj.obj (op T), S.g.hom.app (op T) b = c := by
  let e₂ : Sheaf.H S.X₂ 0 ≃+ S.X₂.obj.obj (op T) := Sheaf.H.equiv₀ S.X₂ hT
  let e₃ : Sheaf.H S.X₃ 0 ≃+ S.X₃.obj.obj (op T) := Sheaf.H.equiv₀ S.X₃ hT
  let g : AddCommGrpCat.of (Sheaf.H S.X₂ 0) ⟶ AddCommGrpCat.of (Sheaf.H S.X₃ 0) :=
    AddCommGrpCat.ofHom (Sheaf.H.map S.g 0)
  let δ : AddCommGrpCat.of (Sheaf.H S.X₃ 0) ⟶ AddCommGrpCat.of (Sheaf.H S.X₁ 1) :=
    AddCommGrpCat.ofHom (Sheaf.H.δ hS 0 1 rfl)
  constructor
  · intro hc
    have hδ : δ.hom (e₃.symm c) = 0 := hc
    exact Sheaf.H.longSequence_equiv₀_exact₃ (hS := hS) (hT := hT) c hδ
  · rintro ⟨b, hb⟩
    let x : Sheaf.H S.X₂ 0 := e₂.symm b
    have hZero : g ≫ δ = 0 := (Sheaf.H.longSequence_exact hS 0 1 rfl).zero 1
    have hδ : δ.hom (g.hom x) = 0 := addCommGrp_comp_zero_apply g δ hZero x
    have hg : g.hom x = e₃.symm c :=
      (Sheaf.H.equiv₀_symm_naturality (f := S.g) (hT := hT) b).trans
        (congrArg e₃.symm hb)
    exact (congrArg δ.hom hg).symm.trans hδ

end GenericSections

/-- A section lifts globally exactly when its boundary vanishes.

In a short exact sheaf sequence, a section of the last sheaf has zero section boundary if and
only if it is the image of a global section of the middle sheaf. -/
theorem smallEtaleSectionBoundary_zero_iff (hS : S.ShortExact)
    (c : S.X₃.obj.obj (op (Scheme.Etale.mk (𝟙 X)))) :
    smallEtaleSectionBoundary.{u, w} hS c = 0 ↔
      ∃ b : S.X₂.obj.obj (op (Scheme.Etale.mk (𝟙 X))),
        S.g.hom.app (op (Scheme.Etale.mk (𝟙 X))) b = c := by
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}
  let : HasExt.{max u w} C := smallEtaleHasExt.{u, w} X
  exact sectionBoundary_zero_iff_atTerminal
    (J := X.smallEtaleTopology) hS (identityEtaleIsTerminal X) c

/-- First global section map of a short exact sequence is injective.

For a short exact sheaf sequence, the first morphism is injective on sections over the
identity étale object. -/
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
