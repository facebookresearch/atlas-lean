/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RealSubanalyticConstructibleModels
public import MathlibExt.AlgebraicGeometry.OrdinarySheafOpenCuts
public import MathlibExt.AlgebraicGeometry.OrdinaryIndDerivedModels
public import MathlibExt.AlgebraicGeometry.BorderedRealSpaceModels
public import Mathlib.Data.EReal.Inv

/-!
# Ordinary extension by zero and constructibility on the compactified real line

The ordinary j! is the native direct image followed by the actual
local-vanishing open cut. Its exact cochain action is localized at Q.
Constructibility is imposed on its cohomology on M times EReal, including
both endpoints. The fixed real compactification uses t on the finite
part, 1/t at positive infinity and -1/t at negative infinity. These are
charts into closed half-spaces, rather than a boundary-free real atlas.
Local finiteness is tested in the original compactified topology.

Source: D'Agnolo--Kashiwara1311.2374v2 Definitions4.9.1--2, printed58;
the standard subanalytic two-point compactification by reciprocal charts.
Mathlib56a005 native sheaf direct image, submodules, Q, cohomology and
EReal, Apache2.0; exactness and Ind comparison proofs are separate Wanted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BorderedRealConstructibleModels

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves OrdinarySheafOpenCuts OrdinaryIndDerivedModels
open SubanalyticCoordinateModels SubanalyticConstructibleSheaves
open MathlibExt.CategoryTheory.NativeBoundedBimoduleModels
open MathlibExt.CategoryTheory.NativeRingedAdjointImageModels

variable (M : Type) [TopologicalSpace M]

abbrev RealInterior := TopCat.of (M × ℝ)
abbrev RealCompactification := TopCat.of (M × EReal)

def finiteRealInclusion : RealInterior M ⟶ RealCompactification M :=
  TopCat.ofHom ⟨fun p => (p.1, (p.2 : EReal)),
    continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)⟩

def finiteRealOpen : Opens (RealCompactification M) :=
  ⟨{p | (⊥ : EReal) < p.2 ∧ p.2 < ⊤}, isOpen_Ioo.preimage continuous_snd⟩

variable [∀ Z : TopCat.{0}, HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]

/-- The actual ordinary j!, with all maps fixed by direct image and local vanishing. -/
def ordinaryCompactifiedExtension :
    OrdinarySheaf ℂ (RealInterior M) ⥤ OrdinarySheaf ℂ (RealCompactification M) :=
  TopCat.Sheaf.pushforward (ModuleCat.{0} ℂ) (finiteRealInclusion M) ⋙
    ordinaryOpenCut ℂ (RealCompactification M) (finiteRealOpen M)

attribute [local instance] HasDerivedCategory.standard

variable [(ordinaryCompactifiedExtension M).Additive]
  (Exact : ExactImageSource (ordinaryCompactifiedExtension M))

/-- Rj! is the exact native localization of the prescribed ordinary j! cochain action. -/
def derivedOrdinaryCompactifiedExtension :
    DerivedCategory (OrdinarySheaf ℂ (RealInterior M)) ⥤
      DerivedCategory (OrdinarySheaf ℂ (RealCompactification M)) :=
  derivedExactImage (ordinaryCompactifiedExtension M) Exact

structure BoundedOrdinaryCompactifiedExtensionSource : Prop where
  bounded : ∀ F : BoundedOrdinary ℂ (RealInterior M),
    IsBoundedDerived (OrdinarySheaf ℂ (RealCompactification M))
      ((derivedOrdinaryCompactifiedExtension M Exact).obj F.obj)

def boundedOrdinaryCompactifiedExtension
    (Bounded : BoundedOrdinaryCompactifiedExtensionSource M Exact) :
    BoundedOrdinary ℂ (RealInterior M) ⥤ BoundedOrdinary ℂ (RealCompactification M) :=
  (IsBoundedDerived (OrdinarySheaf ℂ (RealCompactification M))).lift
    ((IsBoundedDerived (OrdinarySheaf ℂ (RealInterior M))).ι ⋙
      derivedOrdinaryCompactifiedExtension M Exact) Bounded.bounded

/-- The prescribed analytic compactification coordinates, including the two boundary charts. -/
inductive RealTimeChart where
  | finite
  | positiveInfinity
  | negativeInfinity

def timeChartDomain : RealTimeChart → Opens EReal
  | .finite => ⟨Set.Ioo (⊥ : EReal) ⊤, isOpen_Ioo⟩
  | .positiveInfinity => ⟨Set.Ioi (1 : EReal), isOpen_Ioi⟩
  | .negativeInfinity => ⟨Set.Iio (-1 : EReal), isOpen_Iio⟩

def timeChartCoordinate : RealTimeChart → EReal → ℝ
  | .finite => EReal.toReal
  | .positiveInfinity => fun t => t⁻¹.toReal
  | .negativeInfinity => fun t => -t⁻¹.toReal

@[simp] theorem positiveInfinity_coordinate :
    timeChartCoordinate .positiveInfinity ⊤ = 0 := rfl

@[simp] theorem negativeInfinity_coordinate :
    timeChartCoordinate .negativeInfinity ⊥ = 0 := by
  simp [timeChartCoordinate]

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E M]

def compactificationChartDomain (x : M) (T : RealTimeChart) : Set (M × EReal) :=
  (chartAt E x).source ×ˢ (timeChartDomain T : Set EReal)

def compactificationChartCoordinate (x : M) (T : RealTimeChart) : M × EReal → E × ℝ :=
  fun p => ((chartAt E x) p.1, timeChartCoordinate T p.2)

/-- Subanalyticity uses the actual reciprocal boundary images, with endpoint value zero. -/
def IsSubanalyticOnCompactification (S : Set (M × EReal)) : Prop :=
  ∀ (p : M × EReal) (T : RealTimeChart), p.2 ∈ timeChartDomain T →
    IsSubanalyticAt (E × ℝ)
      ((compactificationChartCoordinate M E p.1 T) ''
        (S ∩ compactificationChartDomain M E p.1 T))
      (compactificationChartCoordinate M E p.1 T p)

structure CompactifiedRealSubanalyticPartition where
  index : Type
  stratum : index → Set (M × EReal)
  subanalytic : ∀ i, IsSubanalyticOnCompactification M E (stratum i)
  locallyClosed : ∀ i, IsLocallyClosedSubset (M × EReal) (stratum i)
  disjoint : Pairwise (fun i j => Disjoint (stratum i) (stratum j))
  covers : (⋃ i, stratum i) = Set.univ
  locallyFinite : ∀ p : M × EReal, ∃ U : Opens (M × EReal), p ∈ U ∧
    Set.Finite {i | (stratum i ∩ U).Nonempty}

def compactifiedStratumInclusion (P : CompactifiedRealSubanalyticPartition M E) (i : P.index) :
    TopCat.of (P.stratum i) ⟶ RealCompactification M :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def IsCompactifiedRealConstructible (F : OrdinarySheaf ℂ (RealCompactification M)) : Prop :=
  ∃ P : CompactifiedRealSubanalyticPartition M E, ∀ i : P.index,
    LocallyFiniteRank (TopCat.of (P.stratum i))
      ((TopCat.Sheaf.pullback (ModuleCat.{0} ℂ)
        (compactifiedStratumInclusion M E P i)).obj F)

def IsBoundedCompactifiedRealConstructible
    (F : DerivedCategory (OrdinarySheaf ℂ (RealCompactification M))) : Prop :=
  IsBoundedDerived (OrdinarySheaf ℂ (RealCompactification M)) F ∧
    ∀ i : ℤ, IsCompactifiedRealConstructible M E
      ((DerivedCategory.homologyFunctor (OrdinarySheaf ℂ (RealCompactification M)) i).obj F)

/-- Definition4.9.1 tests the actual ordinary Rj! on the compactification. -/
def IsBorderedRConstructible : ObjectProperty (BoundedOrdinary ℂ (RealInterior M)) := fun F =>
  IsBoundedCompactifiedRealConstructible M E
    ((derivedOrdinaryCompactifiedExtension M Exact).obj F.obj)

abbrev BorderedRConstructibleDerived :=
  (IsBorderedRConstructible M Exact E).FullSubcategory

end MathlibExt.AlgebraicGeometry.BorderedRealConstructibleModels
