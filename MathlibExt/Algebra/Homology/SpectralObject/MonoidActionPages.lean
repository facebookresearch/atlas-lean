/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.SpectralObject.MonoidAction
public import MathlibExt.Algebra.Homology.SpectralObject.Functor
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import MathlibExt.Algebra.Homology.SpectralSequence.Functor
public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import all Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# The pages of an integral monoid module spectral object

The forgetful functor compares the defining short complexes and their
canonical homology. Source first-quadrant support is reflected by faithful
forgetting; no support of the constructed module object is assumed.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

universe v u w t k

variable {M : Type w} [Monoid M]

/-- The next-page bound is derived publicly from the current-page bound
and the successor equation, without a private generated proof. -/
theorem spectralSequenceNextPageBound {r₀ : ℤ} (r r' : ℤ)
    (hrr' : r + 1 = r') (hr : r₀ ≤ r) : r₀ ≤ r' :=
  hrr' ▸ hr.trans (le_add_of_nonneg_right zero_le_one)


private lemma isZero_of_forget (V : ModuleCat.{u} (MonoidAlgebra ℤ M))
    (h : IsZero ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).obj V)) :
    IsZero V := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  apply ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u})).map_injective
  simpa only [Functor.map_id, Functor.map_zero] using h


section Intervals

variable {ι : Type t} [Category.{v} ι]
  (Y : SpectralObject (ModuleCat.{u} (MonoidAlgebra ℤ M)) ι)

/-- The canonical comparison of the module spectral cycles with the cycles
of the forgotten spectral object. -/
def forgetMonoidModuleCyclesIso {i j l : ι} (f : i ⟶ j) (g : j ⟶ l) (n : ℤ) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).obj
      (Y.cycles f g n) ≅ (forgetMonoidModule (M := M) Y).cycles f g n := by
  letI : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectCyclesIso Y f g n

/-- The cycle comparison preserves the original inclusion. -/
@[reassoc]
theorem forgetMonoidModuleCyclesIso_hom_iCycles
    {i j l : ι} (f : i ⟶ j) (g : j ⟶ l) (n : ℤ) :
    (Y.forgetMonoidModuleCyclesIso (M := M) f g n).hom ≫
        (forgetMonoidModule (M := M) Y).iCycles f g n =
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).map
        (Y.iCycles f g n) := by
  let : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectCyclesIso_hom_iCycles Y f g n

/-- The canonical comparison of spectral opcycles under forgetting. -/
def forgetMonoidModuleOpcyclesIso {i j l : ι} (f : i ⟶ j) (g : j ⟶ l) (n : ℤ) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).obj
      (Y.opcycles f g n) ≅ (forgetMonoidModule (M := M) Y).opcycles f g n := by
  letI : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectOpcyclesIso Y f g n

/-- The opcycle comparison preserves the original projection. -/
@[reassoc]
theorem forgetMonoidModuleOpcyclesIso_π
    {i j l : ι} (f : i ⟶ j) (g : j ⟶ l) (n : ℤ) :
    ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u})).map (Y.pOpcycles f g n) ≫
        (Y.forgetMonoidModuleOpcyclesIso (M := M) f g n).hom =
      (forgetMonoidModule (M := M) Y).pOpcycles f g n := by
  let : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectOpcyclesIso_π Y f g n

/-- Forgetting the canonical homology of a spectral short complex gives
the exact original `E` object. -/
def forgetMonoidModuleEIso
    {i j l m : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ l) (f₃ : l ⟶ m)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).obj
        (Y.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) ≅
      (forgetMonoidModule (M := M) Y).E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  letI : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).mapSpectralObjectEIso Y
      f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂

/-- The canonical `E` comparison preserves its cycle quotient projection. -/
@[reassoc]
theorem forgetMonoidModuleEIso_πE
    {i j l m : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ l) (f₃ : l ⟶ m)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).map
        (Y.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) ≫
      (Y.forgetMonoidModuleEIso (M := M) f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom =
    (Y.forgetMonoidModuleCyclesIso (M := M) f₁ f₂ n₁).hom ≫
      (forgetMonoidModule (M := M) Y).πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  let : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectEIso_πE Y f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂

/-- The canonical `E` comparison preserves its opcycle inclusion. -/
@[reassoc]
theorem forgetMonoidModuleEIso_ιE
    {i j l m : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ l) (f₃ : l ⟶ m)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (Y.forgetMonoidModuleEIso (M := M) f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫
      (forgetMonoidModule (M := M) Y).ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).map
      (Y.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) ≫
        (Y.forgetMonoidModuleOpcyclesIso (M := M) f₂ f₃ n₁).hom := by
  let : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectEIso_ιE Y f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂

/-- The opcycle comparison retains its canonical map into interval homology. -/
@[reassoc]
theorem forgetMonoidModuleOpcyclesIso_fromOpcycles
    {i j l : ι} (f : i ⟶ j) (g : j ⟶ l) (fg : i ⟶ l) (hfg : f ≫ g = fg)
    (n : ℤ) :
    (Y.forgetMonoidModuleOpcyclesIso (M := M) f g n).hom ≫
      (forgetMonoidModule (M := M) Y).fromOpcycles f g fg hfg n =
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).map
      (Y.fromOpcycles f g fg hfg n) := by
  let : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectOpcyclesIso_fromOpcycles Y f g fg hfg n

/-- Forgetting retains the spectral cycles-to-opcycles morphism used by
all page differentials. -/
@[reassoc]
theorem forgetMonoidModuleCyclesIso_Ψ
    {i j l m : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ l) (f₃ : l ⟶ m)
    (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).map
      (Y.Ψ f₁ f₂ f₃ n₀ n₁ hn₁) ≫
      (Y.forgetMonoidModuleOpcyclesIso (M := M) f₁ f₂ n₁).hom =
    (Y.forgetMonoidModuleCyclesIso (M := M) f₂ f₃ n₀).hom ≫
      (forgetMonoidModule (M := M) Y).Ψ f₁ f₂ f₃ n₀ n₁ hn₁ := by
  let : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectCyclesIso_Ψ Y f₁ f₂ f₃ n₀ n₁ hn₁

/-- The canonical `E` comparisons commute with the actual spectral
object differential, before any page or first-quadrant specialization. -/
@[reassoc]
theorem forgetMonoidModuleEIso_d
    {i₀ i₁ i₂ i₃ i₄ i₅ : ι}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
    (n₀ n₁ n₂ n₃ : ℤ) (hn₁ : n₀ + 1 = n₁)
    (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).map
      (Y.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃) ≫
      (Y.forgetMonoidModuleEIso (M := M) f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃).hom =
    (Y.forgetMonoidModuleEIso (M := M) f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂).hom ≫
      (forgetMonoidModule (M := M) Y).d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ := by
  let : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).mapSpectralObjectEIso_d
      Y f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃

/-- The `E` comparison commutes with every indexing three-arrow map. -/
@[reassoc]
theorem forgetMonoidModuleEIso_map
    {i₀ i₁ i₂ i₃ j₀ j₁ j₂ j₃ : ι}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (g₁ : j₀ ⟶ j₁) (g₂ : j₁ ⟶ j₂) (g₃ : j₂ ⟶ j₃)
    (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ g₁ g₂ g₃)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).map
        (Y.map f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂) ≫
        (Y.forgetMonoidModuleEIso (M := M) g₁ g₂ g₃ n₀ n₁ n₂ hn₁ hn₂).hom =
      (Y.forgetMonoidModuleEIso (M := M) f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫
        (forgetMonoidModule (M := M) Y).map f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂ := by
  let : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectEIso_map Y f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁
      n₂ hn₁ hn₂

end Intervals


section Pages

variable {ι : Type t} [Preorder ι] {κ : Type k}
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (Y : SpectralObject (ModuleCat.{u} (MonoidAlgebra ℤ M)) ι)
  (data : SpectralSequenceDataCore ι c r₀)

/-- The canonical comparison at every object of a raw spectral page. -/
def forgetMonoidModulePageXIso (r : ℤ) (hr : r₀ ≤ r) (x : κ) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).obj
      (SpectralSequence.pageX Y data r x hr) ≅
    SpectralSequence.pageX (forgetMonoidModule (M := M) Y) data r x hr := by
  letI : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectPageXIso Y data r hr x

/-- The page comparison commutes with the canonical change of presentation
as an `E` object, including all degree and index equality casts. -/
@[reassoc]
theorem forgetMonoidModulePageXIso_presented
    (r : ℤ) (hr : r₀ ≤ r) (x : κ) (i₀ i₁ i₂ i₃ : ι)
    (h₀ : i₀ = data.i₀ r x hr) (h₁ : i₁ = data.i₁ x)
    (h₂ : i₂ = data.i₂ x) (h₃ : i₃ = data.i₃ r x hr)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg x)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (Y.forgetMonoidModulePageXIso (M := M) data r hr x).hom ≫
      (SpectralSequence.pageXIso (forgetMonoidModule (M := M) Y) data r hr x
        i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).hom =
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).map
      (SpectralSequence.pageXIso Y data r hr x
        i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).hom ≫
      (Y.forgetMonoidModuleEIso (M := M)
        (homOfLE (data.le₀₁' r hr x h₀ h₁)) (homOfLE (data.le₁₂' x h₁ h₂))
        (homOfLE (data.le₂₃' r hr x h₂ h₃)) n₀ n₁ n₂ hn₁ hn₂).hom := by
  let : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectPageXIso_presented Y data r hr x i₀ i₁ i₂ i₃ h₀
      h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂

/-- Inverse presentation changes also commute with the canonical page
comparison. -/
@[reassoc]
theorem forgetMonoidModulePageXIso_presented_inv
    (r : ℤ) (hr : r₀ ≤ r) (x : κ) (i₀ i₁ i₂ i₃ : ι)
    (h₀ : i₀ = data.i₀ r x hr) (h₁ : i₁ = data.i₁ x)
    (h₂ : i₂ = data.i₂ x) (h₃ : i₃ = data.i₃ r x hr)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg x)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).map
      (SpectralSequence.pageXIso Y data r hr x
        i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).inv ≫
      (Y.forgetMonoidModulePageXIso (M := M) data r hr x).hom =
    (Y.forgetMonoidModuleEIso (M := M)
      (homOfLE (data.le₀₁' r hr x h₀ h₁)) (homOfLE (data.le₁₂' x h₁ h₂))
      (homOfLE (data.le₂₃' r hr x h₂ h₃)) n₀ n₁ n₂ hn₁ hn₂).hom ≫
      (SpectralSequence.pageXIso (forgetMonoidModule (M := M) Y) data r hr x
        i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).inv := by
  let : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectPageXIso_presented_inv Y data r hr x i₀ i₁ i₂ i₃
      h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂

/-- Every raw page differential commutes with the canonical object
comparisons. The statement includes the zero maps outside the shape relation. -/
@[reassoc]
theorem forgetMonoidModulePageXIso_d
    (r : ℤ) (hr : r₀ ≤ r) (x y : κ) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).map
      (SpectralSequence.pageD Y data r x y hr) ≫
      (Y.forgetMonoidModulePageXIso (M := M) data r hr y).hom =
    (Y.forgetMonoidModulePageXIso (M := M) data r hr x).hom ≫
      SpectralSequence.pageD (forgetMonoidModule (M := M) Y) data r x y hr := by
  let : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectPageXIso_d Y data r hr x y

/-- The canonical object comparisons assemble into a page-complex
isomorphism, before requiring the successor-page support conditions. -/
def forgetMonoidModulePageIso (r : ℤ) (hr : r₀ ≤ r) :
    ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).mapHomologicalComplex
      (c r)).obj (SpectralSequence.page Y data r hr) ≅
    SpectralSequence.page (forgetMonoidModule (M := M) Y) data r hr := by
  letI : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).mapSpectralObjectPageIso
      Y data r hr

/-- The page-complex comparison has exactly the canonical `E` comparison
as each component. -/
@[simp]
theorem forgetMonoidModulePageIso_hom_f (r : ℤ) (hr : r₀ ≤ r) (x : κ) :
    (Y.forgetMonoidModulePageIso (M := M) data r hr).hom.f x =
      (Y.forgetMonoidModulePageXIso (M := M) data r hr x).hom := by
  let : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectPageIso_hom_f Y data r hr x

end Pages


section SupportedPages

variable {ι : Type t} [Preorder ι] {κ : Type k}
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (Y : SpectralObject (ModuleCat.{u} (MonoidAlgebra ℤ M)) ι)
  (data : SpectralSequenceDataCore ι c r₀)
  [Y.HasSpectralSequence data]

/-- Forgetting scalars preserves both boundary-vanishing conditions of the
source spectral sequence. -/
instance forgetMonoidModule_hasSpectralSequence :
    (forgetMonoidModule (M := M) Y).HasSpectralSequence data := by
  let : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObject_hasSpectralSequence Y data

unseal spectralSequence in
/-- The canonical comparison on the actual supported spectral page. -/
def forgetMonoidModuleSpectralSequencePageIso (r : ℤ) (hr : r₀ ≤ r) :
    ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).mapHomologicalComplex
      (c r)).obj ((Y.spectralSequence data).page r hr) ≅
    ((forgetMonoidModule (M := M) Y).spectralSequence data).page r hr := by
  letI : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectSpectralSequencePageIso Y data r hr

unseal spectralSequence in
/-- The supported page isomorphism retains every canonical object comparison. -/
@[simp]
theorem forgetMonoidModuleSpectralSequencePageIso_hom_f
    (r : ℤ) (hr : r₀ ≤ r) (x : κ) :
    (Y.forgetMonoidModuleSpectralSequencePageIso (M := M) data r hr).hom.f x =
      (Y.forgetMonoidModulePageXIso (M := M) data r hr x).hom := by
  let : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectSpectralSequencePageIso_hom_f Y data r hr x

end SupportedPages

section SequenceCongruence

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type t} [Preorder ι] {κ : Type k}
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (Y : SpectralObject C ι) (data : SpectralSequenceDataCore ι c r₀)
  [Y.HasSpectralSequence data]

private theorem spectralSequence_congr (Z : SpectralObject C ι)
    [Z.HasSpectralSequence data] (h : Y = Z) :
    Y.spectralSequence data = Z.spectralSequence data := by
  subst Z
  rfl

end SequenceCongruence


section SupportedSuccessors

variable {ι : Type t} [Preorder ι] {κ : Type k}
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (Y : SpectralObject (ModuleCat.{u} (MonoidAlgebra ℤ M)) ι)
  (data : SpectralSequenceDataCore ι c r₀)
  [Y.HasSpectralSequence data]

unseal spectralSequence in
/-- The canonical comparison of supported pages commutes with the actual
successor homology isomorphisms, at all positions including missing neighbors. -/
theorem forgetMonoidModuleSpectralSequencePageIso_comm
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (x : κ) :
    HomologicalComplex.homologyMap
        (Y.forgetMonoidModuleSpectralSequencePageIso (M := M) data r hr).hom x ≫
      (((forgetMonoidModule (M := M) Y).spectralSequence data).iso
        r r' x hrr' hr).hom =
    (((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).mapSpectralSequence
        (Y.spectralSequence data)).iso r r' x hrr' hr).hom ≫
      (Y.forgetMonoidModuleSpectralSequencePageIso (M := M)
        data r' (by omega)).hom.f x := by
  let : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectSpectralSequencePageIso_comm Y data r r' hrr' hr x

/-- The supported module spectral sequence, forgotten with the canonical
homology comparison, is isomorphic to the sequence of its underlying groups. -/
def forgetMonoidModuleSpectralSequenceIso :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).mapSpectralSequence
      (Y.spectralSequence data) ≅
    (forgetMonoidModule (M := M) Y).spectralSequence data := by
  letI : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectSpectralSequenceIso Y data

/-- The whole sequence comparison has the specified canonical page maps. -/
@[simp]
theorem forgetMonoidModuleSpectralSequenceIso_hom_hom (r : ℤ) (hr : r₀ ≤ r) :
    (Y.forgetMonoidModuleSpectralSequenceIso (M := M) data).hom.hom r hr =
      (Y.forgetMonoidModuleSpectralSequencePageIso (M := M) data r hr).hom := by
  let : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectSpectralSequenceIso_hom_hom Y data r hr

end SupportedSuccessors

section Support

variable {ι : Type t} [Preorder ι] {κ : Type k}
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (E : SpectralObject AddCommGrpCat.{u} ι) (ρ : M →* End E)
  (data : SpectralSequenceDataCore ι c r₀)
  [E.HasSpectralSequence data]

/-- The original sequence's boundary support gives the support of its
constructed monoid-module spectral object by faithful forgetting. -/
instance monoidModule_hasSpectralSequence : (E.monoidModule ρ).HasSpectralSequence data where
  isZero_H_obj_mk₁_i₀_le r r' x hx n hn hrr' hr := by
    apply isZero_of_forget (M := M)
    change IsZero (((forgetMonoidModule (M := M) (E.monoidModule ρ)).H n).obj
      (mk₁ (homOfLE (data.i₀_le r r' x hrr' hr))))
    rw [E.forgetMonoidModule_monoidModule ρ]
    exact E.isZero_H_obj_mk₁_i₀_le data r r' hrr' hr x hx n hn
  isZero_H_obj_mk₁_i₃_le r r' x hx n hn hrr' hr := by
    apply isZero_of_forget (M := M)
    change IsZero (((forgetMonoidModule (M := M) (E.monoidModule ρ)).H n).obj
      (mk₁ (homOfLE (data.i₃_le r r' x hrr' hr))))
    rw [E.forgetMonoidModule_monoidModule ρ]
    exact E.isZero_H_obj_mk₁_i₃_le data r r' hrr' hr x hx n hn

/-- The genuine monoid-module spectral sequence constructed from the
original recipe and the derived module support. -/
def monoidModuleSpectralSequence : SpectralSequence (ModuleCat.{u} (MonoidAlgebra ℤ M)) c r₀ :=
  (E.monoidModule ρ).spectralSequence data

/-- The actual native successor, with the next-page bound explicit in
its public type so ordinary consumers can use its linear-map interface. -/
@[no_expose]
def monoidModuleSpectralSequenceSuccessorIso
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (x : κ) :
    ((E.monoidModuleSpectralSequence ρ data).page r hr).homology x ≅
      ((E.monoidModuleSpectralSequence ρ data).page r'
        (spectralSequenceNextPageBound r r' hrr' hr)).X x :=
  (E.monoidModuleSpectralSequence ρ data).iso r r' x hrr' hr

/-- The public successor accessor is exactly the original native
spectral-object successor, with no new choice of homology data. -/
theorem monoidModuleSpectralSequenceSuccessorIso_eq
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (x : κ) :
    E.monoidModuleSpectralSequenceSuccessorIso ρ data r r' hrr' hr x =
      (E.monoidModuleSpectralSequence ρ data).iso r r' x hrr' hr := by
  rfl

/-- The actual successor is linear for every monoid-algebra scalar. -/
theorem monoidModuleSpectralSequenceSuccessorIso_map_smul
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (x : κ)
    (s : MonoidAlgebra ℤ M)
    (z : ((E.monoidModuleSpectralSequence ρ data).page r hr).homology x) :
    (E.monoidModuleSpectralSequenceSuccessorIso ρ data r r' hrr' hr x).hom (s • z) =
      s • (E.monoidModuleSpectralSequenceSuccessorIso ρ data r r' hrr' hr x).hom z :=
  (E.monoidModuleSpectralSequenceSuccessorIso ρ data r r' hrr' hr x).hom.hom.map_smul s z

/-- Forgetting the constructed monoid-module sequence recovers the original
whole spectral sequence through its canonical page and homology comparisons. -/
def monoidModuleSpectralSequenceForgetIso :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).mapSpectralSequence
      (E.monoidModuleSpectralSequence ρ data) ≅ E.spectralSequence data :=
  (E.monoidModule ρ).forgetMonoidModuleSpectralSequenceIso (M := M) data ≪≫
    eqToIso (by
      exact spectralSequence_congr _ data E (E.forgetMonoidModule_monoidModule ρ))

/-- The canonical underlying-group comparison of every actual module page. -/
def monoidModulePageForgetIso (r : ℤ) (hr : r₀ ≤ r) :
    ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).mapHomologicalComplex
      (c r)).obj ((E.monoidModuleSpectralSequence ρ data).page r hr) ≅
    (E.spectralSequence data).page r hr :=
  (SpectralSequence.pageFunctor AddCommGrpCat.{u} c r₀ r hr).mapIso
    (E.monoidModuleSpectralSequenceForgetIso ρ data)

/-- The whole forget isomorphism retains exactly the chosen page comparison. -/
@[simp]
theorem monoidModuleSpectralSequenceForgetIso_hom_hom (r : ℤ) (hr : r₀ ≤ r) :
    (E.monoidModuleSpectralSequenceForgetIso ρ data).hom.hom r hr =
      (E.monoidModulePageForgetIso ρ data r hr).hom := rfl

end Support

end CategoryTheory.Abelian.SpectralObject

end
