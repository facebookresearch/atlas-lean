/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.Algebra.Homology.SpectralObjectMap
public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# Maps between pages of spectral objects

A morphism of abelian spectral objects commutes with the differential between
their `E` objects.  Consequently, for fixed spectral-sequence data and a fixed
page index, the objectwise `EMap`s assemble into a morphism of homological
complexes.

This file does not prove compatibility with successor-page homology
isomorphisms and does not construct a `SpectralSequence.Hom`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits ComposableArrows

universe v u vι uι vκ uκ

namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type uι} [Category.{vι} ι]
variable {X Y Z : SpectralObject C ι}

namespace Hom

private noncomputable def cyclesMap (phi : X ⟶ Y)
    {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ) :
    X.cycles f g n ⟶ Y.cycles f g n :=
  kernel.lift _
    (X.iCycles f g n ≫ (phi.hom n).app (mk₁ g)) (by
      rw [Category.assoc, ← phi.comm n (n + 1) rfl f g,
        ← Category.assoc, X.iCycles_δ f g n (n + 1) rfl, zero_comp])

@[reassoc (attr := simp)]
private theorem cyclesMap_iCycles (phi : X ⟶ Y)
    {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ) :
    cyclesMap phi f g n ≫ Y.iCycles f g n =
      X.iCycles f g n ≫ (phi.hom n).app (mk₁ g) :=
  kernel.lift_ι _ _ _

private noncomputable def opcyclesMap (phi : X ⟶ Y)
    {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ) :
    X.opcycles f g n ⟶ Y.opcycles f g n :=
  cokernel.desc _
    ((phi.hom n).app (mk₁ f) ≫ Y.pOpcycles f g n) (by
      rw [← Category.assoc, phi.comm (n - 1) n (by lia) f g,
        Category.assoc, Y.δ_pOpcycles f g (n - 1) n (by lia), comp_zero])

@[reassoc (attr := simp)]
private theorem pOpcycles_opcyclesMap (phi : X ⟶ Y)
    {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ) :
    X.pOpcycles f g n ≫ opcyclesMap phi f g n =
      (phi.hom n).app (mk₁ f) ≫ Y.pOpcycles f g n :=
  cokernel.π_desc _ _ _

private theorem cyclesIso_inv_cyclesMap (phi : X ⟶ Y)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv ≫
        ShortComplex.cyclesMap
          (shortComplexMap phi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) =
      cyclesMap phi f₁ f₂ n₁ ≫
        (Y.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv := by
  rw [← cancel_mono
    (Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).iCycles]
  simp

private theorem opcyclesMap_opcyclesIso_hom (phi : X ⟶ Y)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex.opcyclesMap
          (shortComplexMap phi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) ≫
        (Y.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom =
      (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫
        opcyclesMap phi f₂ f₃ n₁ := by
  rw [← cancel_epi
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).pOpcycles]
  simp

@[reassoc]
private theorem πE_EMap (phi : X ⟶ Y)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
        EMap phi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      cyclesMap phi f₁ f₂ n₁ ≫
        Y.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  simp only [SpectralObject.πE, EMap, Category.assoc,
    ShortComplex.homologyπ_naturality]
  rw [← Category.assoc,
    cyclesIso_inv_cyclesMap phi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂,
    Category.assoc]

@[reassoc]
private theorem EMap_ιE (phi : X ⟶ Y)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    EMap phi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
        Y.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
        opcyclesMap phi f₂ f₃ n₁ := by
  change ShortComplex.homologyMap
        (shortComplexMap phi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) ≫
      ((Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).homologyι ≫
        (Y.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom) =
    ((X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).homologyι ≫
      (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom) ≫
        opcyclesMap phi f₂ f₃ n₁
  rw [← Category.assoc, ShortComplex.homologyι_naturality,
    Category.assoc,
    opcyclesMap_opcyclesIso_hom phi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂,
    ← Category.assoc]

@[reassoc]
private theorem opcyclesMap_fromOpcycles (phi : X ⟶ Y)
    {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (fg : i ⟶ k)
    (hfg : f ≫ g = fg) (n : ℤ) :
    opcyclesMap phi f g n ≫ Y.fromOpcycles f g fg hfg n =
      X.fromOpcycles f g fg hfg n ≫ (phi.hom n).app (mk₁ fg) := by
  rw [← cancel_epi (X.pOpcycles f g n),
    pOpcycles_opcyclesMap_assoc, Y.p_fromOpcycles,
    X.p_fromOpcycles_assoc]
  exact ((phi.hom n).naturality (twoδ₂Toδ₁ f g fg hfg)).symm

@[reassoc]
private theorem cyclesMap_Ψ_opcyclesMap (phi : X ⟶ Y)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) :
    cyclesMap phi f₂ f₃ n₀ ≫ Y.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ =
      X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ ≫
        opcyclesMap phi f₁ f₂ n₁ := by
  rw [← cancel_mono (Y.fromOpcycles f₁ f₂ (f₁ ≫ f₂) rfl n₁)]
  calc
    (cyclesMap phi f₂ f₃ n₀ ≫
          Y.Ψ f₁ f₂ f₃ n₀ n₁ hn₁) ≫
        Y.fromOpcycles f₁ f₂ (f₁ ≫ f₂) rfl n₁ =
      cyclesMap phi f₂ f₃ n₀ ≫
        (Y.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ ≫
          Y.fromOpcycles f₁ f₂ (f₁ ≫ f₂) rfl n₁) :=
      Category.assoc _ _ _
    _ = cyclesMap phi f₂ f₃ n₀ ≫
        (Y.iCycles f₂ f₃ n₀ ≫
          Y.δ (f₁ ≫ f₂) f₃ n₀ n₁ hn₁) := by
      rw [Y.Ψ_fromOpcycles f₁ f₂ f₃ (f₁ ≫ f₂) rfl n₀ n₁ hn₁]
    _ = (cyclesMap phi f₂ f₃ n₀ ≫
          Y.iCycles f₂ f₃ n₀) ≫
        Y.δ (f₁ ≫ f₂) f₃ n₀ n₁ hn₁ :=
      (Category.assoc _ _ _).symm
    _ = (X.iCycles f₂ f₃ n₀ ≫
          (phi.hom n₀).app (mk₁ f₃)) ≫
        Y.δ (f₁ ≫ f₂) f₃ n₀ n₁ hn₁ := by
      rw [cyclesMap_iCycles]
    _ = X.iCycles f₂ f₃ n₀ ≫
        ((phi.hom n₀).app (mk₁ f₃) ≫
          Y.δ (f₁ ≫ f₂) f₃ n₀ n₁ hn₁) :=
      Category.assoc _ _ _
    _ = X.iCycles f₂ f₃ n₀ ≫
        (X.δ (f₁ ≫ f₂) f₃ n₀ n₁ hn₁ ≫
          (phi.hom n₁).app (mk₁ (f₁ ≫ f₂))) := by
      rw [← phi.comm n₀ n₁ hn₁ (f₁ ≫ f₂) f₃]
    _ = (X.iCycles f₂ f₃ n₀ ≫
          X.δ (f₁ ≫ f₂) f₃ n₀ n₁ hn₁) ≫
        (phi.hom n₁).app (mk₁ (f₁ ≫ f₂)) :=
      (Category.assoc _ _ _).symm
    _ = (X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ ≫
          X.fromOpcycles f₁ f₂ (f₁ ≫ f₂) rfl n₁) ≫
        (phi.hom n₁).app (mk₁ (f₁ ≫ f₂)) := by
      rw [X.Ψ_fromOpcycles f₁ f₂ f₃ (f₁ ≫ f₂) rfl n₀ n₁ hn₁]
    _ = X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ ≫
        (X.fromOpcycles f₁ f₂ (f₁ ≫ f₂) rfl n₁ ≫
          (phi.hom n₁).app (mk₁ (f₁ ≫ f₂))) :=
      Category.assoc _ _ _
    _ = X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ ≫
        (opcyclesMap phi f₁ f₂ n₁ ≫
          Y.fromOpcycles f₁ f₂ (f₁ ≫ f₂) rfl n₁) := by
      rw [opcyclesMap_fromOpcycles]
    _ = (X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ ≫
          opcyclesMap phi f₁ f₂ n₁) ≫
        Y.fromOpcycles f₁ f₂ (f₁ ≫ f₂) rfl n₁ :=
      (Category.assoc _ _ _).symm

/-- A morphism of spectral objects commutes with the differential between
their `E` objects. -/
theorem EMap_d (phi : X ⟶ Y)
    {i₀ i₁ i₂ i₃ i₄ i₅ : ι}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
    (n₀ n₁ n₂ n₃ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) :
    EMap phi f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂ ≫
        Y.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ =
      X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
        EMap phi f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃ := by
  rw [← cancel_epi (X.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂),
    ← cancel_mono (Y.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃)]
  slice_lhs 1 2 =>
    rw [πE_EMap phi f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂]
  slice_lhs 2 4 =>
    rw [Y.πE_d_ιE f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃]
  rw [cyclesMap_Ψ_opcyclesMap phi f₂ f₃ f₄ n₁ n₂ hn₂]
  slice_rhs 3 4 =>
    rw [EMap_ιE phi f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃]
  slice_rhs 1 3 =>
    rw [X.πE_d_ιE f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃]

end Hom

section PageMap

variable {ι' : Type uι} [Preorder ι']
variable {κ : Type uκ} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
variable {X' Y' Z' : SpectralObject C ι'}

namespace Hom

private theorem EMap_heq_of_eq (phi : X' ⟶ Y')
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ι'}
    (ha₀ : a₀ = b₀) (ha₁ : a₁ = b₁)
    (ha₂ : a₂ = b₂) (ha₃ : a₃ = b₃)
    (f₁ : a₀ ⟶ a₁) (f₂ : a₁ ⟶ a₂) (f₃ : a₂ ⟶ a₃)
    (g₁ : b₀ ⟶ b₁) (g₂ : b₁ ⟶ b₂) (g₃ : b₂ ⟶ b₃)
    {m₀ m₁ m₂ n₀ n₁ n₂ : ℤ}
    (hm₀ : m₀ = n₀) (hm₁ : m₁ = n₁) (hm₂ : m₂ = n₂)
    (hm₁' : m₀ + 1 = m₁) (hm₂' : m₁ + 1 = m₂)
    (hn₁' : n₀ + 1 = n₁) (hn₂' : n₁ + 1 = n₂) :
    HEq (EMap phi f₁ f₂ f₃ m₀ m₁ m₂ hm₁' hm₂')
      (EMap phi g₁ g₂ g₃ n₀ n₁ n₂ hn₁' hn₂') := by
  subst b₀
  subst b₁
  subst b₂
  subst b₃
  subst n₀
  subst n₁
  subst n₂
  have hf₁ : f₁ = g₁ := Subsingleton.elim _ _
  have hf₂ : f₂ = g₂ := Subsingleton.elim _ _
  have hf₃ : f₃ = g₃ := Subsingleton.elim _ _
  subst g₁
  subst g₂
  subst g₃
  exact HEq.rfl

/-- The component at `pq` of the page map induced by a morphism of spectral
objects. -/
noncomputable def pageMapComponent (phi : X' ⟶ Y')
    (data : SpectralSequenceDataCore ι' c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    SpectralSequence.pageX X' data r pq hr ⟶
      SpectralSequence.pageX Y' data r pq hr :=
  EMap phi
    (homOfLE (data.le₀₁ r pq))
    (homOfLE (data.le₁₂ pq))
    (homOfLE (data.le₂₃ r pq))
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)

/-- The objectwise page maps commute with every page differential.  The
non-`Rel` case is the zero square. -/
theorem pageMapComponent_comm (phi : X' ⟶ Y')
    (data : SpectralSequenceDataCore ι' c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) :
    pageMapComponent phi data r hr pq ≫
        SpectralSequence.pageD Y' data r pq pq' hr =
      SpectralSequence.pageD X' data r pq pq' hr ≫
        pageMapComponent phi data r hr pq' := by
  by_cases hpq : (c r).Rel pq pq'
  · dsimp [pageMapComponent, SpectralSequence.pageD]
    rw [dite_eq_left hpq, dite_eq_left hpq]
    have hD := EMap_d phi
        (homOfLE (data.le₀₁ r pq'))
        (homOfLE (data.le₁₂' pq' rfl (data.hc₀₂ r pq pq' hpq)))
        (homOfLE (data.le₀₁ r pq))
        (homOfLE (data.le₁₂ pq))
        (homOfLE (data.le₂₃ r pq))
        (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)
        (data.deg pq + 2) (by lia) rfl (by lia)
    rw [← Category.assoc, hD, Category.assoc, Category.assoc]
    congr 1
    dsimp [pageMapComponent, SpectralSequence.pageXIso]
    apply eq_of_heq
    refine HEq.trans (comp_eqToHom_heq _ _) ?_
    refine HEq.trans ?_ (eqToHom_comp_heq _ _).symm
    exact EMap_heq_of_eq phi rfl rfl
      (data.hc₀₂ r pq pq' hpq hr)
      (data.hc₁₃ r pq pq' hpq hr)
      (homOfLE (data.le₀₁ r pq'))
      (homOfLE (data.le₁₂' pq' rfl (data.hc₀₂ r pq pq' hpq)))
      (homOfLE (data.le₀₁ r pq))
      (homOfLE (data.le₀₁ r pq'))
      (homOfLE (data.le₁₂ pq'))
      (homOfLE (data.le₂₃ r pq'))
      (by have h := data.hc r pq pq' hpq hr; lia)
      (data.hc r pq pq' hpq hr)
      (by have h := data.hc r pq pq' hpq hr; lia)
      (by lia) (by lia) (by lia) (by lia)
  · simp [SpectralSequence.pageD, hpq]

/-- A morphism of spectral objects induces a morphism between their fixed raw
pages. -/
noncomputable def pageMap (phi : X' ⟶ Y')
    (data : SpectralSequenceDataCore ι' c r₀)
    (r : ℤ) (hr : r₀ ≤ r) :
    SpectralSequence.page X' data r hr ⟶
      SpectralSequence.page Y' data r hr where
  f pq := pageMapComponent phi data r hr pq
  comm' pq pq' _ := pageMapComponent_comm phi data r hr pq pq'

@[simp]
theorem pageMap_id (X' : SpectralObject C ι')
    (data : SpectralSequenceDataCore ι' c r₀)
    (r : ℤ) (hr : r₀ ≤ r) :
    pageMap (𝟙 X') data r hr = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext pq
  exact EMap_id X'
    (homOfLE (data.le₀₁ r pq))
    (homOfLE (data.le₁₂ pq))
    (homOfLE (data.le₂₃ r pq))
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)

@[reassoc, simp]
theorem pageMap_comp (phi : X' ⟶ Y') (psi : Y' ⟶ Z')
    (data : SpectralSequenceDataCore ι' c r₀)
    (r : ℤ) (hr : r₀ ≤ r) :
    pageMap (phi ≫ psi) data r hr =
      pageMap phi data r hr ≫ pageMap psi data r hr := by
  apply HomologicalComplex.Hom.ext
  funext pq
  exact EMap_comp phi psi
    (homOfLE (data.le₀₁ r pq))
    (homOfLE (data.le₁₂ pq))
    (homOfLE (data.le₂₃ r pq))
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)

end Hom

/-- The raw page construction at a fixed page index is functorial in the
spectral object. -/
noncomputable def spectralObjectPageFunctor
    (data : SpectralSequenceDataCore ι' c r₀)
    (r : ℤ) (hr : r₀ ≤ r) :
    SpectralObject C ι' ⥤ HomologicalComplex C (c r) where
  obj X := SpectralSequence.page X data r hr
  map phi := phi.pageMap data r hr
  map_id X := Hom.pageMap_id X data r hr
  map_comp phi psi := Hom.pageMap_comp phi psi data r hr

end PageMap

universe t k

section NativePageMap
universe uNative vNative tNative kNative
variable {D : Type uNative} [Category.{vNative} D] [Abelian D]
  {ι : Type tNative} [Preorder ι] {κ : Type kNative} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  {X Y : SpectralObject D ι}

unseal SpectralObject.spectralSequence in
/-- The actual native fixed-page map is the existing raw page map, on the
native page complexes. Both boundary-support premises belong to the original
spectral objects; no page map or comparison is supplied. -/
def Hom.spectralSequencePageMap (φ : X ⟶ Y)
    (data : SpectralObject.SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data]
    (r : ℤ) (hr : r₀ ≤ r) :
    (X.spectralSequence data).page r hr ⟶ (Y.spectralSequence data).page r hr :=
  φ.pageMap data r hr

end NativePageMap

unseal SpectralObject.spectralSequence in
/-- The native page-map component is the original raw E-map through the
canonical native-page presentations at the recipe's own indices and degrees. -/
theorem Hom.spectralSequencePageMap_f
    {D : Type u} [Category.{v} D] [Abelian D]
    {ι : Type t} [Preorder ι] {κ : Type k} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
    {X Y : SpectralObject D ι} (φ : X ⟶ Y)
    (data : SpectralObject.SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data]
    (r : ℤ) (hr : r₀ ≤ r) (x : κ) :
    (φ.spectralSequencePageMap data r hr).f x ≫
        (Y.spectralSequencePageXIso data r hr x
          (data.i₀ r x) (data.i₁ x) (data.i₂ x) (data.i₃ r x)
          rfl rfl rfl rfl
          (data.deg x - 1) (data.deg x) (data.deg x + 1) rfl
          (sub_add_cancel _ _) rfl).hom =
      (X.spectralSequencePageXIso data r hr x
          (data.i₀ r x) (data.i₁ x) (data.i₂ x) (data.i₃ r x)
          rfl rfl rfl rfl
          (data.deg x - 1) (data.deg x) (data.deg x + 1) rfl
          (sub_add_cancel _ _) rfl).hom ≫
        φ.pageMapComponent data r hr x := by
  -- Reduce only producer-scoped native/raw definitions and the existing
  -- canonical presentation to the identical E-map.
  simp only [Hom.spectralSequencePageMap, Hom.pageMap,
    SpectralObject.spectralSequencePageXIso, SpectralObject.SpectralSequence.pageXIso,
    eqToIso_refl, Iso.refl_hom]
  exact (Category.comp_id (φ.pageMapComponent data r hr x)).trans
    (Category.id_comp (φ.pageMapComponent data r hr x)).symm

end CategoryTheory.Abelian.SpectralObject

end
