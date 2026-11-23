/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.Constant
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate

/-!
# Positive category-homology vanishing on an initial category

An initial object contracts the nerve to the zero simplex.  Simplicial
homotopy invariance and the dimension bound for `Δ[0]` therefore kill positive
ordinary category homology.  Together with the constant comparison, the same
holds for any coefficient functor that inverts all morphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe w v u vA uA

namespace SSet

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
  [HasCoproducts.{w} A] [CategoryWithHomology A]
  {X Y : SSet.{w}}

/-- Explicit simplicial homotopy inverse data induces an isomorphism on
simplicial homology. -/
noncomputable def homologyIsoOfHomotopyEquiv
    (f : X ⟶ Y) (g : Y ⟶ X)
    (hX : SSet.Homotopy (f ≫ g) (𝟙 X))
    (hY : SSet.Homotopy (g ≫ f) (𝟙 Y))
    (R : A) (n : ℕ) : X.homology R n ≅ Y.homology R n where
  hom := SSet.homologyMap f R n
  inv := SSet.homologyMap g R n
  hom_inv_id := by
    rw [← SSet.homologyMap_comp, hX.congr_homologyMap R n,
      SSet.homologyMap_id]
  inv_hom_id := by
    rw [← SSet.homologyMap_comp, hY.congr_homologyMap R n,
      SSet.homologyMap_id]

end SSet

namespace CategoryTheory.CategoryHomology

variable {C : Type u} [Category.{v} C]
  {A : Type uA} [Category.{vA} A]

/-- The nerve of a category with an initial object is connected. -/
theorem nerveIsConnectedOfIsInitial {i : C} (hi : IsInitial i) :
    (nerve C).IsConnected := by
  rw [SSet.isConnected_iff]
  constructor
  · constructor
    intro a b
    induction a using SSet.π₀.rec with
    | mk x =>
      induction b using SSet.π₀.rec with
      | mk y =>
        have hx : SSet.π₀.mk (nerveEquiv.symm i) = SSet.π₀.mk x :=
          (SSet.π₀.sound (nerve.edgeMk
            (hi.to (nerveEquiv x)))).trans
              (congrArg SSet.π₀.mk (nerveEquiv.symm_apply_apply x))
        have hy : SSet.π₀.mk (nerveEquiv.symm i) = SSet.π₀.mk y :=
          (SSet.π₀.sound (nerve.edgeMk
            (hi.to (nerveEquiv y)))).trans
              (congrArg SSet.π₀.mk (nerveEquiv.symm_apply_apply y))
        exact hx.symm.trans hy
  · exact ⟨ComposableArrows.mk₀ i⟩

section

variable [Preadditive A]
  [HasCoproducts.{max u v} A] [CategoryWithHomology A]

/-- The nerve of a category with an initial object has the homology of
`Δ[0]`. -/
noncomputable def nerveInitialHomologyIso {i : C} (hi : IsInitial i)
    (R : A) (n : ℕ) :
    (nerve C).homology R n ≅ (Δ[0] : SSet.{max u v}).homology R n := by
  let N : SSet.{max u v} := nerve C
  let q : N ⟶ (Δ[0] : SSet.{max u v}) :=
    SSet.stdSimplex.isTerminalObj₀.from N
  let s : (Δ[0] : SSet.{max u v}) ⟶ N :=
    SSet.const (ComposableArrows.mk₀ i)
  let η : (Functor.const C).obj i ⟶ 𝟭 C :=
    { app := fun X ↦ hi.to X
      naturality := by
        intro X Y f
        exact hi.hom_ext _ _ }
  have hqs : q ≫ s =
      CategoryTheory.nerveMap ((Functor.const C).obj i) := by
    ext D Z
    rfl
  have hX : SSet.Homotopy (q ≫ s) (𝟙 N) := by
    rw [hqs]
    simpa only [CategoryTheory.nerveMap_id] using
      (CategoryTheory.NatTrans.nerveHomotopy η)
  have hsq : s ≫ q = 𝟙 (Δ[0] : SSet.{max u v}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hY : SSet.Homotopy (s ≫ q)
      (𝟙 (Δ[0] : SSet.{max u v})) := by
    rw [hsq]
    change SSet.RelativeMorphism.Homotopy
      (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))
      (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))
    exact SSet.RelativeMorphism.Homotopy.refl _
  exact SSet.homologyIsoOfHomotopyEquiv q s hX hY R n

/-- Positive homology of the nerve of a category with an initial object
vanishes. -/
theorem isZero_nerveHomology_of_isInitial {i : C} (hi : IsInitial i)
    (R : A) (n : ℕ) (hn : 1 ≤ n) :
    IsZero ((nerve C).homology R n) := by
  have hZero : IsZero (((Δ[0] : SSet.{max u v}).homology R n)) :=
    SSet.isZero_homology_of_hasDimensionLT
      (Δ[0] : SSet.{max u v}) R n 1 hn
  exact IsZero.of_iso hZero (nerveInitialHomologyIso hi R n)

/-- Degree-zero homology of the nerve of a category with an initial object
is the coefficient object. -/
noncomputable def nerveInitialHomologyZeroIso {i : C} (hi : IsInitial i)
    (R : A) : (nerve C).homology R 0 ≅ R := by
  letI : (nerve C).IsConnected := nerveIsConnectedOfIsInitial hi
  exact asIso ((nerve C).homology₀ε R)

end

section

variable [Abelian A] [HasCoproducts.{max u v} A]
  (M : CategoryTheory.Functor C A)
  [∀ {X Y : C} (f : X ⟶ Y), IsIso (M.map f)]

/-- Degree-zero category homology with morphism-inverting coefficients on an
initial category is the value of the coefficient functor at the initial
object. -/
noncomputable def homologyWithCoefficientsZeroIsoOfIsInitial
    (i : C) (hi : IsInitial i) :
    homologyWithCoefficients M 0 ≅ M.obj i :=
  (homologyWithCoefficientsIsoConstOfIsInitial M i hi 0).symm ≪≫
    homologyWithConstantCoefficientsIso C A (M.obj i) 0 ≪≫
    nerveInitialHomologyZeroIso hi (M.obj i)

/-- Positive category homology with morphism-inverting coefficients vanishes
on a category with an initial object. -/
theorem isZero_homologyWithCoefficients_of_isInitial
    (i : C) (hi : IsInitial i) (n : ℕ) (hn : 1 ≤ n) :
    IsZero (homologyWithCoefficients M n) := by
  have hZero : IsZero ((nerve C).homology (M.obj i) n) :=
    isZero_nerveHomology_of_isInitial hi (M.obj i) n hn
  let e : homologyWithCoefficients M n ≅
      (nerve C).homology (M.obj i) n :=
    (homologyWithCoefficientsIsoConstOfIsInitial M i hi n).symm ≪≫
      homologyWithConstantCoefficientsIso C A (M.obj i) n
  exact IsZero.of_iso hZero e

end
end CategoryTheory.CategoryHomology

end
