/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.AlgebraicGeometry.WaldhausenExactFlags
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Topology.Homotopy.Equiv
/-!
# Coherent S-construction carriers, support and actual restriction maps

On a Noetherian scheme, coherent modules are the finitely presented sheaves
of modules. Zero objects are listed explicitly in the predicate so that the
base flag is constructed without an additional finite-presentation instance.
The supported category consists of those coherent sheaves whose actual
restriction to the indicated open is zero. It includes torsion sheaves.

Higher groups are the homotopy groups of the actual based geometric
realization of the exact flags. The restriction inputs below are literal
exactness/coherence properties of Mathlib's restriction functor. They do not
assume a localization or descent theorem. The topology on the homotopy fibre
and pullback is the actual subspace topology on paths with fixed endpoints.

References: D. Quillen, *Higher algebraic K-theory I* (1973), §§4--5;
F. Waldhausen, *Algebraic K-theory of spaces* (1985), §1.3.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.CoherentGTheory
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.WaldhausenExactFlags
open scoped ZeroObject

def coherent (X : Scheme.{0}) : ObjectProperty X.Modules := fun F =>
  IsZero F ∨ SheafOfModules.IsFinitePresentation F

def supported (X : Scheme.{0}) (U : X.Opens) : ObjectProperty X.Modules := fun F =>
  IsZero F ∨ (SheafOfModules.IsFinitePresentation F ∧
    IsZero ((Scheme.Modules.restrictFunctor U.ι).obj F))

theorem supported_coherent (X : Scheme.{0}) (U : X.Opens) (F : X.Modules)
    (h : supported X U F) : coherent X F := h.imp id And.left

abbrev gSpace (X : Scheme.{0}) := SSet.toTop.obj (diagonal (coherent X))
abbrev supportedSpace (X : Scheme.{0}) (U : X.Opens) := SSet.toTop.obj (diagonal (supported X U))
abbrev gBase (X : Scheme.{0}) := basePoint (coherent X) (Or.inl (isZero_zero _))
abbrev supportedBase (X : Scheme.{0}) (U : X.Opens) :=
  basePoint (supported X U) (Or.inl (isZero_zero _))
abbrev HigherG (X : Scheme.{0}) (n : ℕ) :=
  HigherGroup (coherent X) (Or.inl (isZero_zero _)) n

def supportedInclusion (X : Scheme.{0}) (U : X.Opens) : supportedSpace X U ⟶ gSpace X :=
  SSet.toTop.map (mapDiagonal (supported X U) (coherent X) (𝟭 X.Modules)
    (supported_coherent X U))

class RestrictionCoherent (X : Scheme.{0}) (U : X.Opens) : Prop where
  [additive : (Scheme.Modules.restrictFunctor U.ι).Additive]
  [limits : PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.ι)]
  [colimits : PreservesFiniteColimits (Scheme.Modules.restrictFunctor U.ι)]
  preserves : ∀ F : X.Modules, coherent X F →
    coherent U ((Scheme.Modules.restrictFunctor U.ι).obj F)
attribute [instance] RestrictionCoherent.additive RestrictionCoherent.limits
  RestrictionCoherent.colimits

def restriction (X : Scheme.{0}) (U : X.Opens) [RestrictionCoherent X U] :
    gSpace X ⟶ gSpace U :=
  SSet.toTop.map (mapDiagonal (coherent X) (coherent U) (Scheme.Modules.restrictFunctor U.ι)
    (RestrictionCoherent.preserves (X := X) (U := U)))

abbrev homotopyFiber {Z W : TopCat.{1}} (f : Z ⟶ W) (w : W) :=
  {z : Z × C(unitInterval, W) | z.2 0 = f z.1 ∧ z.2 1 = w}

def fiberProjection {Z W : TopCat.{1}} (f : Z ⟶ W) (w : W) :
    C(homotopyFiber f w, Z) :=
  ⟨fun z => z.1.1, continuous_fst.comp continuous_subtype_val⟩

class OpenRestrictionCoherent {X U : Scheme.{0}} (i : U ⟶ X)
    [IsOpenImmersion i] : Prop where
  [additive : (Scheme.Modules.restrictFunctor i).Additive]
  [limits : PreservesFiniteLimits (Scheme.Modules.restrictFunctor i)]
  [colimits : PreservesFiniteColimits (Scheme.Modules.restrictFunctor i)]
  preserves : ∀ F : X.Modules, coherent X F →
    coherent U ((Scheme.Modules.restrictFunctor i).obj F)
attribute [instance] OpenRestrictionCoherent.additive OpenRestrictionCoherent.limits
  OpenRestrictionCoherent.colimits

def openRestriction {X U : Scheme.{0}} (i : U ⟶ X)
    [IsOpenImmersion i] [OpenRestrictionCoherent i] : gSpace X ⟶ gSpace U :=
  SSet.toTop.map (mapDiagonal (coherent X) (coherent U) (Scheme.Modules.restrictFunctor i)
    (OpenRestrictionCoherent.preserves (i := i)))

abbrev homotopyPullback {X Y Z : TopCat.{1}} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  {p : X × Y × C(unitInterval, Z) | p.2.2 0 = f p.1 ∧ p.2.2 1 = g p.2.1}

def pullbackFirst {X Y Z : TopCat.{1}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    C(homotopyPullback f g, X) :=
  ⟨fun p => p.1.1, continuous_fst.comp continuous_subtype_val⟩

def pullbackSecond {X Y Z : TopCat.{1}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    C(homotopyPullback f g, Y) :=
  ⟨fun p => p.1.2.1, continuous_fst.comp (continuous_snd.comp continuous_subtype_val)⟩

end MathlibExt.AlgebraicGeometry.CoherentGTheory
