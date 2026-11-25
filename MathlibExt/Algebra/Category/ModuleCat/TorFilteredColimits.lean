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
# Native Tor and exact filtered module colimits

Balance lets us resolve the fixed coefficient. The resulting degreewise
tensor functors preserve colimits, and filtered module colimits are exact.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u w w'

namespace ModuleCat

variable {R : Type u} [CommRing R]
variable (J : Type w) [Category.{w'} J] [IsFiltered J] [UnivLE.{w, u}] [UnivLE.{w', u}]

/-- Native Tor with any fixed coefficient preserves filtered colimits. The
object and morphism universes of the shape can be chosen independently. -/
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

/-- The native Tor of a filtered colimit vanishes if it vanishes at every stage. -/
theorem tor_isZero_of_isColimit {D : J ⥤ ModuleCat.{u} R} {c : Cocone D}
    (hc : IsColimit c) (M : ModuleCat.{u} R) (n : ℕ)
    (h : ∀ j, IsZero (((Tor (ModuleCat.{u} R) n).obj M).obj (D.obj j))) :
    IsZero (((Tor (ModuleCat.{u} R) n).obj M).obj c.pt) := by
  let F := (Tor (ModuleCat.{u} R) n).obj M
  let : PreservesColimitsOfShape J F := tor_preservesFilteredColimitsOfShape J M n
  exact (isColimitOfPreserves F hc).isZero_pt ((D ⋙ F).isZero_iff.mpr h)

end ModuleCat
