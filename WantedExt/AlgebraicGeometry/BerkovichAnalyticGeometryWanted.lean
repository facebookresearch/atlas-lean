/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.BerkovichAnalyticCategory
public import MathlibExt.AlgebraicGeometry.AffinoidFormalModels
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# General Berkovich analytification and its normalized comparisons

These requests supply the missing global geometric contracts on actual
valued points, restricted-series quotient rings, weak topologies and sheaves.
Paper tasks may bind the public interfaces and their named local dependencies
while the shared providers are proved. The point functor, affinoid spectrum,
rational-limit presheaf, normalized Γ–Spec map, module pullback, derived
comparison are completed code in MathlibExt. The realization category is
the completed assembly from explicit bounded identity/composition closure
proofs; those geometric closure proofs are separate Wanted requests.

The rational-spectrum goal is a comparison with weak real-seminorm topology.
It does not request TauCeti's already implemented rational fraction rings,
classical-point subdomains, adic local restrictions or global adic gluing.
The real-valued affine point map is constrained by every actual coordinate;
the global sheaf charts retain the entire polynomial ideal and nilpotents.

Primary locators: Berkovich, *Spectral theory and analytic geometry over
non-Archimedean fields* (1990), §2.2 and §§3.4–3.5, including Theorems
3.4.8(ii) and 3.5.3(ii) for properness. The publicly read exposition is
Zomervrucht, *Berkovich analytification*, the unnumbered affinoid/section
formulas and Remark 1.1, Definition 1.2, formula (2.3),
Theorem 2.1, Proposition 2.7 and Theorems 2.8–2.9, pp. 1–3:
https://www.mi.fu-berlin.de/math/groups/arithmetic_geometry/research_seminar/documents/berkovich03.pdf
Hrushovski–Loeser–Poonen, *Berkovich spaces embed in Euclidean spaces*,
Remark 1.5, p. 2, independently states the proper compact Hausdorff theorem:
https://people.math.harvard.edu/~demarco/Math295/HrushovskiLoeserPoonen_Berkovich.pdf
For the formal-model construction and reduction, see Berkovich, *Vanishing
cycles for formal schemes*, Invent. Math. 115 (1994), §1,
https://doi.org/10.1007/BF01231772.

General non-good analytic G-spaces, global formal-model/Raynaud equivalence,
rigid/adic category comparisons, skeletons and six-functor comparisons remain
further contracts. The good realization here covers all algebraic schemes
locally of finite type, including singular and nonreduced schemes.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.BerkovichAnalyticGeometryWanted

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.NonarchimedeanAnalyticSpaces
open MathlibExt.AlgebraicGeometry.BerkovichStructureSheaf
open MathlibExt.AlgebraicGeometry.NonarchimedeanAnalyticGeometry
open MathlibExt.AlgebraicGeometry.BerkovichAnalyticCategory
open MathlibExt.AlgebraicGeometry.BerkovichAnalytification
open MathlibExt.AlgebraicGeometry.AffinoidFormalModels
open MathlibExt.AlgebraicGeometry.BoundedAffinoidMorphisms

def_wanted rational_spectrum_geometry (K : Type) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (A : AffinoidAlgebra K)
    (R : RationalRestrictionTheory A) : RationalSpectrumGeometry R

def_wanted affinoid_sheaf_geometry (K : Type) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (A : AffinoidAlgebra K)
    (R : RationalRestrictionTheory A) (G : RationalSpectrumGeometry R) :
    AffinoidSheafGeometry R G

def_wanted affine_point_comparison (K : Type) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (X : AlgebraicScheme K)
    (T : AffineTateChart K X) (R : RationalRestrictionTheory T.algebra)
    (G : RationalSpectrumGeometry R) (S : AffinoidSheafGeometry R G) :
    T.PointComparison S

def_wanted bounded_affinoid_morphism (K : Type) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (A B : AffinoidAlgebra K)
    (RA : RationalRestrictionTheory A) (RB : RationalRestrictionTheory B)
    (GA : RationalSpectrumGeometry RA) (GB : RationalSpectrumGeometry RB)
    (SA : AffinoidSheafGeometry RA GA) (SB : AffinoidSheafGeometry RB GB)
    (f : B ⟶ A) : AffinoidMorphism SA SB f

theorem_wanted bounded_composition (K : Type) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K]
    (_localTheory : LocalAffinoidTheory K) : BoundedComposition K

def_wanted algebraic_realization (K : Type) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K]
    (_localTheory : LocalAffinoidTheory K) (X : AlgebraicScheme K)
    [LocallyOfFiniteType X.hom] : AnalyticSpace X

def_wanted analytic_morphism (K : Type) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (X Y : AlgebraicScheme K)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (A : AnalyticSpace X) (B : AnalyticSpace Y) (f : X ⟶ Y) : A.Morphism B f

def_wanted global_analytification (K : Type) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K]
    (_localTheory : LocalAffinoidTheory K) [BoundedComposition K] :
    SchemeAnalytification K

theorem_wanted coherent_pullback (K : Type) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (X : AlgebraicScheme K)
    [LocallyOfFiniteType X.hom] (A : AnalyticSpace X) : A.CoherentPullback

theorem_wanted proper_gaga (K : Type) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (X : AlgebraicScheme K)
    [IsProper X.hom] (A : AnalyticSpace X) : A.GAGA

theorem_wanted proper_cohomology_comparison (K : Type) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (X : AlgebraicScheme K)
    [IsProper X.hom] (A : AnalyticSpace X)
    [PreservesFiniteLimits A.pullback] (F : X.left.Modules)
    [F.IsFinitePresentation] (n : ℤ) :
    Function.Bijective (A.cohomologyComparison F n)

theorem_wanted proper_analytic_compactness (K : Type) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (X : AlgebraicScheme K)
    [IsProper X.hom] : CompactSpace (space K X) ∧ T2Space (space K X)

def_wanted formal_reduction_comparison (R : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (K : Type) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [Algebra R K] [IsFractionRing R K]
    (π : R) (_uniformizer : Irreducible π)
    (_integralBase : ∀ r : R, ‖algebraMap R K r‖ ≤ 1)
    (_topologicallyNilpotent : ‖algebraMap R K π‖ < 1)
    (M : AffinoidFormalModel R K π) : M.ReductionComparison

end WantedExt.AlgebraicGeometry.BerkovichAnalyticGeometryWanted
