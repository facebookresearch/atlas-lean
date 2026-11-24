/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialPresheaf.ConstantEvaluation
public import MathlibExt.AlgebraicTopology.SimplicialObject.FinitePowerSite

/-!
# Constant extension and ordered all-zero evaluation

Specialize the terminal-site enriched adjunction to the original finite
simplex-power source. Every inner scalar universe is retained, including at
height zero. These are raw presheaf maps, without a localized model choice.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalClosed Opposite
open scoped Simplicial

namespace SimplicialPresheaf.OrderedJFS.ConstantEvaluation

/-- The shared all-zero source object at the same original finite height. -/
abbrev zeroTuple (n : ℕ) : FinitePowerSite.Source n := FinitePowerSite.zeroTuple n

/-- The shared original operator family to the all-zero source object. -/
abbrev toZero {n : ℕ} (a : FinitePowerSite.Source n) : a ⟶ zeroTuple n :=
  FinitePowerSite.toZero a

/-- The shared terminal witness for the all-zero source object. -/
abbrev zeroIsTerminal (n : ℕ) : IsTerminal (zeroTuple n) :=
  FinitePowerSite.zeroIsTerminal n

/-- The native Hom universe of the finite simplex-power site is zero. -/
local instance sourceLocallySmall (n : ℕ) : LocallySmall.{u} (FinitePowerSite.Source n) :=
  @CategoryTheory.locallySmall_of_univLE _ _ UnivLE.zero

/-- Constant extension on the original site retains the entire scalar. -/
abbrev constant (n : ℕ) : SSet.{u} ⥤ SimplicialPresheaf.{u} (FinitePowerSite.Source n) :=
  SimplicialPresheaf.ConstantEvaluation.constant

/-- Evaluate the original diagram at its ordered all-zero tuple. -/
abbrev evaluation (n : ℕ) : SimplicialPresheaf.{u} (FinitePowerSite.Source n) ⥤ SSet.{u} :=
  SimplicialPresheaf.ConstantEvaluation.evaluation (zeroTuple n)

/-- The existing terminal-site adjunction at the same ordered all-zero tuple. -/
def adjunction (n : ℕ) : constant n ⊣ evaluation n :=
  SimplicialPresheaf.ConstantEvaluation.adjunction (zeroIsTerminal n)

/-- Ordinary transposition evaluates the same original natural map at zero. -/
theorem adjunction_homEquiv (n : ℕ) (K : SSet.{u})
    (X : SimplicialPresheaf.{u} (FinitePowerSite.Source n))
    (f : (constant n).obj K ⟶ X) :
    (adjunction n).homEquiv K X f = f.app (op (zeroTuple n)) :=
  SimplicialPresheaf.ConstantEvaluation.adjunction_homEquiv (zeroIsTerminal n) K X f

/-- The original enriched end is the scalar Hom into the all-zero value. -/
def iso (n : ℕ) (K : SSet.{u}) (X : SimplicialPresheaf.{u} (FinitePowerSite.Source n)) :
    innerHom ((constant n).obj K) X ≅ (ihom K).obj (X.obj (op (zeroTuple n))) :=
  SimplicialPresheaf.ConstantEvaluation.iso (zeroIsTerminal n) K X

/-- The forward comparison is the exact original zero-tuple projection. -/
theorem iso_hom (n : ℕ) (K : SSet.{u})
    (X : SimplicialPresheaf.{u} (FinitePowerSite.Source n)) :
    (iso n K X).hom = innerHomπ ((constant n).obj K) X (op (zeroTuple n)) :=
  rfl

/-- The inverse projects along the original ordered operators, then their one opposite. -/
theorem iso_inv_projection (n : ℕ) (K : SSet.{u})
    (X : SimplicialPresheaf.{u} (FinitePowerSite.Source n))
    (a : (FinitePowerSite.Source n)ᵒᵖ) :
    (iso n K X).inv ≫ innerHomπ ((constant n).obj K) X a =
      (ihom K).map (X.map (toZero a.unop).op) := by
  have h : (zeroIsTerminal n).from a.unop = toZero a.unop :=
    (zeroIsTerminal n).hom_ext _ _
  simpa only [iso, h] using
    SimplicialPresheaf.ConstantEvaluation.iso_inv_projection (zeroIsTerminal n) K X a

/-- Scalar precomposition retains the same ordered zero comparison. -/
theorem iso_source (n : ℕ) {K L : SSet.{u}} (k : K ⟶ L)
    (X : SimplicialPresheaf.{u} (FinitePowerSite.Source n)) :
    innerHomPre ((constant n).map k) X ≫ (iso n K X).hom =
      (iso n L X).hom ≫ (pre k).app (X.obj (op (zeroTuple n))) :=
  SimplicialPresheaf.ConstantEvaluation.iso_source (zeroIsTerminal n) k X

/-- Target postcomposition uses the scalar Hom of the actual zero component. -/
theorem iso_target (n : ℕ) (K : SSet.{u})
    {X Y : SimplicialPresheaf.{u} (FinitePowerSite.Source n)} (f : X ⟶ Y) :
    innerHomPost ((constant n).obj K) f ≫ (iso n K Y).hom =
      (iso n K X).hom ≫ (ihom K).map (f.app (op (zeroTuple n))) :=
  SimplicialPresheaf.ConstantEvaluation.iso_target (zeroIsTerminal n) K f

/-- Target naturality is packaged using the same chosen enriched end. -/
def natIso (n : ℕ) (K : SSet.{u}) :
    innerHomFunctor.obj (op ((constant n).obj K)) ≅ evaluation n ⋙ ihom K :=
  SimplicialPresheaf.ConstantEvaluation.natIso (zeroIsTerminal n) K

/-- The empty-coordinate case compares directly with the scalar internal Hom. -/
def zeroIso (K L : SSet.{u}) :
    innerHom ((constant 0).obj K) ((constant 0).obj L) ≅ (ihom K).obj L :=
  iso 0 K ((constant 0).obj L)

/-- At height zero, every inverse projection is the identity scalar map. -/
theorem zeroIso_inv_projection (K L : SSet.{u}) (a : (FinitePowerSite.Source 0)ᵒᵖ) :
    (zeroIso K L).inv ≫ innerHomπ ((constant 0).obj K) ((constant 0).obj L) a =
      𝟙 ((ihom K).obj L) :=
  (iso_inv_projection 0 K ((constant 0).obj L) a).trans ((ihom K).map_id L)

end SimplicialPresheaf.OrderedJFS.ConstantEvaluation
