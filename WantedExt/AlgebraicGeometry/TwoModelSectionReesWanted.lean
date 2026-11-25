/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.TwoModelSectionRees
public import Batteries.Util.ProofWanted

/-!
# Exact two-model section-Rees comparison

Blum--Xu arXiv1812.03538v2, §§3--4.
The ring is the actual filtered-section subalgebra; the parameter,
grading and Proj maps are fixed. Generic Rees/Proj construction laws
are source-covered; these obligations pin their realization to the
actual two-DVR-model section maps and coefficient images.

Finite generation and full special-section base change are explicit
intermediate inputs. This does not infer them from a free stability
predicate or assert that every filtration has a log-Fano central fibre.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.TwoModelSectionRees

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DVRSectionLattices
open MathlibExt.AlgebraicGeometry.DVRGradedSectionFamilies
open MathlibExt.AlgebraicGeometry.ProjectiveLineSystems

theorem_wanted twoModelReesCoefficientComparison
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (D : TwoModels (R := R) (K := K))
    [IsProper D.first.hom] [Flat D.first.hom]
    [IsProper D.second.hom] [Flat D.second.hom]
    (C : D.GradedComparisons) (u : Uniformizer (R := R) (K := K))
    {n : ℕ} (A : SpecialCoordinates D n) : A.HasReesCoefficients C u

def_wanted projectiveTwoModelReesRealization
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    (D : TwoModels (R := R) (K := K))
    [IsProper D.first.hom] [Flat D.first.hom]
    [IsProper D.second.hom] [Flat D.second.hom]
    (C : D.GradedComparisons) (u : Uniformizer (R := R) (K := K))
    {n : ℕ} (A : SpecialCoordinates D n) [IsProper A.variety.X.hom]
    (L : ProjectiveLineSystems.LineBundle A.variety.X.left)
    (normalized : L.val = A.series.line) (ample : ProjectiveLineSystems.IsAmpleLine L)
    (full : ∀ m, Function.Surjective (D.firstSpecial m).map)
    (G : SpecialCoordinates.ReesGrading A C u)
    (finite :
      letI := A.parameterAlgebra C u
      Algebra.FiniteType (Polynomial (IsLocalRing.ResidueField R)) (A.reesAlgebra C u)) :
    G.Realization

end MathlibExt.AlgebraicGeometry.TwoModelSectionRees
