/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import MathlibExt.Algebra.Category.ModuleCat.ExactFilteredColimits
public import MathlibExt.Algebra.Category.ModuleCat.TorBalancedUniverse
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.BifunctorColimits

/-!
# Tor and filtered colimits of modules

Let `R : Type u` be a commutative ring and `J` a filtered category whose object and morphism
universes are bounded by `u`. For a fixed `M : ModuleCat.{u} R` and any natural degree `n`,
the functor `Tor_n^R(M, -)` preserves colimits of shape `J`.

Consequently, if `Tor_n^R(M, D j)` vanishes at every object of a filtered diagram `D`, then it
also vanishes at its colimit. The comparison uses the balance of tensor derivations and
exactness of filtered module colimits.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u w w'

namespace ModuleCat

variable {R : Type u} [CommRing R]
variable (J : Type w) [Category.{w'} J] [IsFiltered J] [UnivLE.{w, u}] [UnivLE.{w', u}]

/-- Tor with a fixed module preserves filtered colimits.

For a filtered category `J` with both index universes bounded by the module universe `u`, the
functor `Tor_n^R(M, -)` on `ModuleCat.{u} R` preserves colimits of shape `J` for every natural
`n`. -/
theorem tor_preservesFilteredColimitsOfShape (M : ModuleCat.{u} R) (n : ℕ) :
    PreservesColimitsOfShape J ((Tor (ModuleCat.{u} R) n).obj M) := by
  let C := ModuleCat.{u} R
  let : HasExactColimitsOfShape J C := hasExactFilteredColimitsOfShape R J
  let F : C ⥤ C ⥤ C := (curriedTensor C).flip
  let : ∀ X : C, (F.flip.obj X).Additive := fun X =>
    inferInstanceAs (tensorLeft X).Additive
  let : ∀ X : C, PreservesColimitsOfShape J (F.obj X) := fun X =>
    preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)
  let : PreservesColimitsOfShape J ((F.leftDerivedBifunctor n).obj M) :=
    F.leftDerivedBifunctor_obj_preservesColimitsOfShape J M n
  let e : ((Tor C n).obj M) ≅ (F.leftDerivedBifunctor n).obj M :=
    (UniverseTensor.nativeTorSymmetryNatIso.{u, 0} R n).app M
  exact preservesColimitsOfShape_of_natIso e.symm

variable {J}

/-- Objectwise Tor vanishing passes to a filtered colimit.

Let `c` be a colimit cocone of a filtered diagram `D` in `ModuleCat.{u} R`. If `Tor_n^R(M,
D.obj j)` is zero for every `j`, then `Tor_n^R(M, c.pt)` is zero. -/
theorem tor_isZero_of_isColimit {D : J ⥤ ModuleCat.{u} R} {c : Cocone D}
    (hc : IsColimit c) (M : ModuleCat.{u} R) (n : ℕ)
    (h : ∀ j, IsZero (((Tor (ModuleCat.{u} R) n).obj M).obj (D.obj j))) :
    IsZero (((Tor (ModuleCat.{u} R) n).obj M).obj c.pt) := by
  let F := (Tor (ModuleCat.{u} R) n).obj M
  let : PreservesColimitsOfShape J F := tor_preservesFilteredColimitsOfShape J M n
  exact (isColimitOfPreserves F hc).isZero_pt ((D ⋙ F).isZero_iff.mpr h)

end ModuleCat
