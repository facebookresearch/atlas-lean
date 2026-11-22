/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.CoproductWeakEquivalences
public import MathlibExt.AlgebraicTopology.ModelCategory.FibrantProducts
public import MathlibExt.CategoryTheory.Limits.SourceObjectTransport
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Original coproduct source mapping and cofibrant cofans

The complete generic declarations are retained from the original native
Omega weak-class source. Original universes, chosen fans/cofans, maps,
hypotheses and proof bodies are unchanged.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v w uC vC uD vD uV vV uI uT
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OriginalCoproductSourceMapping

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {J : Type w} [HasProductsOfShape J D] (F : Cᵒᵖ ⥤ D)
  [PreservesLimitsOfSize.{w, w} F]

/-- The literal source map of every actual caller coproduct is weak
when all original mapping components are fibrant weak maps. -/
theorem originalCallerMap_weak {X Y : J → C}
    [∀ j, IsFibrant (F.obj (Opposite.op (X j)))]
    [∀ j, IsFibrant (F.obj (Opposite.op (Y j)))]
    (c : Cofan X) (hc : IsColimit c) (d : Cofan Y) (hd : IsColimit d)
    (f : ∀ j, X j ⟶ Y j) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.inj j ≫ p = f j ≫ d.inj j)
    (hf : ∀ j, WeakEquivalence (F.map (f j).op)) : WeakEquivalence (F.map p.op) := by
  let cF := CategoryTheory.OriginalDiscreteSourceMapping.fan F c
  let dF := CategoryTheory.OriginalDiscreteSourceMapping.fan F d
  have h (j : J) : F.map p.op ≫ cF.proj j = dF.proj j ≫ F.map (f j).op := by
    have hOp : p.op ≫ (c.inj j).op = (d.inj j).op ≫ (f j).op :=
      congrArg Quiver.Hom.op (hp j)
    exact (F.map_comp _ _).symm.trans ((F.congr_map hOp).trans (F.map_comp _ _))
  exact originalFanMap_weak_of_fibrant dF
    (CategoryTheory.OriginalDiscreteSourceMapping.fanIsLimit F d hd) cF
    (CategoryTheory.OriginalDiscreteSourceMapping.fanIsLimit F c hc)
    (fun j => F.map (f j).op) (F.map p.op) h hf

end HomotopicalAlgebra.OriginalCoproductSourceMapping

namespace HomotopicalAlgebra.OriginalSourceObjectWeakTransport

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {J : Type w} [HasProductsOfShape J D]
  (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfSize.{w, w} F]
  (O : C → D) (hO : O = fun X => F.obj (Opposite.op X))

/-- The entire actual weak-map algorithm follows the original endpoint function equality. -/
theorem callerMap_weak {X Y : J → C}
    [∀ j, IsFibrant (O (X j))] [∀ j, IsFibrant (O (Y j))]
    (c : Cofan X) (hc : IsColimit c) (d : Cofan Y) (hd : IsColimit d)
    (f : ∀ j, X j ⟶ Y j) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.inj j ≫ p = f j ≫ d.inj j)
    (hf : ∀ j, WeakEquivalence (CategoryTheory.OriginalSourceObjectTransport.pre F O hO (f j))) :
    WeakEquivalence (CategoryTheory.OriginalSourceObjectTransport.pre F O hO p) := by
  cases hO
  have hf' : ∀ j, WeakEquivalence (F.map (f j).op) := by
    intro j
    simpa only [CategoryTheory.OriginalSourceObjectTransport.pre,
      CategoryTheory.OriginalSourceObjectTransport.iso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
      Category.id_comp, Category.comp_id] using hf j
  simpa only [CategoryTheory.OriginalSourceObjectTransport.pre,
    CategoryTheory.OriginalSourceObjectTransport.iso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id] using
      OriginalCoproductSourceMapping.originalCallerMap_weak F c hc d hd f p hp hf'

end HomotopicalAlgebra.OriginalSourceObjectWeakTransport

namespace CategoryTheory.OriginalSourceObjectTransport

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {J : Type w} [HasProductsOfShape J D]
  (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfSize.{w, w} F]
  (O : C → D) (hO : O = fun X => F.obj (Opposite.op X))
  (P : ∀ {X Y : C}, (X ⟶ Y) → (O Y ⟶ O X))
  (hP : HEq (fun (X Y : C) (f : X ⟶ Y) => @P X Y f)
    (fun (X Y : C) (f : X ⟶ Y) => F.map f.op))

include hO hP in
/-- The exact actual pre-map function yields weak source mapping of every caller coproduct. -/
theorem callerMap_weak {X Y : J → C}
    [∀ j, IsFibrant (O (X j))] [∀ j, IsFibrant (O (Y j))]
    (c : Cofan X) (hc : IsColimit c) (d : Cofan Y) (hd : IsColimit d)
    (f : ∀ j, X j ⟶ Y j) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.inj j ≫ p = f j ≫ d.inj j)
    (hf : ∀ j, WeakEquivalence (P (f j))) : WeakEquivalence (P p) := by
  have hg : ∀ j, WeakEquivalence (pre F O hO (f j)) := by
    intro j
    rw [pre_eq F O hO P hP]
    exact hf j
  have h := HomotopicalAlgebra.OriginalSourceObjectWeakTransport.callerMap_weak
    F O hO c hc d hd f p hp hg
  rw [pre_eq F O hO P hP] at h
  exact h

end CategoryTheory.OriginalSourceObjectTransport
