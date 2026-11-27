/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.SkeletalTropicalDegree

/-!
# Global skeleton, torus factorization and skeletal degree

Gubler--Rabinoff--Werner, *Skeletons and tropicalizations*, 1404.7044v3,
Definition 3.1, Theorem 4.13, Proposition 8.2 and Theorem 8.4.
Actual proper pairs, model charts, residue strata, Shilov fibres, torus
characters, generic-fibre degree and lattice indices fix every construction.
Retraction/deformation, affine slopes, factorization and the degree formula
are requested conclusions. No semistable-model existence or tropical section
is assumed. The generic point avoids every canonical-cell image of dimension
less than dim(X), including collapsed maximal cells.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.GlobalSemistableSkeletonWanted

open CategoryTheory
open MathlibExt.AlgebraicGeometry.SemistableFormalAtlas
open MathlibExt.AlgebraicGeometry.GlobalSemistableSkeleton
open MathlibExt.AlgebraicGeometry.SkeletalTropicalDegree
open MathlibExt.AlgebraicGeometry.ValuativeTropicalization
open MathlibExt.AlgebraicGeometry.TropicalCycleIntersections
open MathlibExt.AlgebraicGeometry.AnalyticTropicalSupport

/- The native-completion/residue-valued Berkovich adapter is an exact
construction boundary beyond the positively credited ordinary adic gluing. -/
def_wanted generic_reduction_atlas (K : Type) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsAlgClosed K] (P : StrictPair K) : GlobalAtlas P

def_wanted global_retraction (K : Type) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsAlgClosed K] (P : StrictPair K) (A : GlobalAtlas P) :
    GlobalRetraction P A

def_wanted strong_deformation (K : Type) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsAlgClosed K] (P : StrictPair K) (A : GlobalAtlas P)
    (R : GlobalRetraction P A) : StrongDeformation P A R

theorem_wanted chart_skeletal_compatibility (K : Type) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsAlgClosed K] (P : StrictPair K) (A : GlobalAtlas P)
    (i j : Fin P.atlasSize) (q : (P.chart i).model.GenericPoint)
    (r : (P.chart j).model.GenericPoint) (_same : (A.chart i).map q = (A.chart j).map r) :
    q ∈ localSkeleton (P.chart i) (A.chart i).reduction ↔
      r ∈ localSkeleton (P.chart j) (A.chart j).reduction

def_wanted adapted_cells (K : Type) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsAlgClosed K] (P : StrictPair K) (A : GlobalAtlas P) :
    ∀ S : GlobalStratum P, AdaptedCell P A S

def_wanted integral_torus_slopes (K : Type) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsAlgClosed K] (P : StrictPair K) (A : GlobalAtlas P)
    (F : ∀ S : GlobalStratum P, AdaptedCell P A S) (m : ℕ) (I : Ideal (CoordinateRing K m))
    (phi : complementScheme P ⟶ subscheme I) : IntegralSlopes P A F m I phi

theorem_wanted slope_lattice_independent (K : Type) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsAlgClosed K] (P : StrictPair K) (A : GlobalAtlas P)
    (F : ∀ S : GlobalStratum P, AdaptedCell P A S) (m : ℕ) (I : Ideal (CoordinateRing K m))
    (phi : complementScheme P ⟶ subscheme I) (L M : IntegralSlopes P A F m I phi)
    (S : GlobalStratum P) : latticeHom P A F m I phi L S = latticeHom P A F m I phi M S

theorem_wanted tropical_factorization (K : Type) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsAlgClosed K] (P : StrictPair K) (A : GlobalAtlas P)
    (R : GlobalRetraction P A) (m : ℕ) (I : Ideal (CoordinateRing K m))
    (phi : complementScheme P ⟶ subscheme I)
    (p : MathlibExt.AlgebraicGeometry.BerkovichAnalytification.Point K (complementScheme P)) :
    torusVector P m I phi (retractedDomain P A R p) = torusVector P m I phi p

theorem_wanted skeletal_tropical_image (K : Type) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsAlgClosed K] (P : StrictPair K) (A : GlobalAtlas P)
    (m : ℕ) (I : Ideal (CoordinateRing K m)) [I.IsPrime]
    (phi : complementScheme P ⟶ subscheme I) (_image : DenseRange phi.left) :
    tropicalization K m I = skeletalImage P A m I phi

theorem_wanted skeletal_Sturmfels_Tevelev (K : Type) [NormedField K] [IsUltrametricDist K]
    [Valued K NNReal] [CompleteSpace K] [IsAlgClosed K]
    (_norm : ValuationNormCompatibility K) (_nontrivial : NontrivialValuation K)
    (P : StrictPair K) (A : GlobalAtlas P) (F : ∀ S : GlobalStratum P, AdaptedCell P A S)
    (m : ℕ) (I : Ideal (CoordinateRing K m)) [I.IsPrime]
    (phi : complementScheme P ⟶ subscheme I) (_finite : GenericallyFinite P m I phi)
    (L : IntegralSlopes P A F m I phi) (Y : Presentation K m I)
    (_dimension : Y.cycle.dimension = P.dimension) (tau : Fin Y.cycle.complex.count)
    (_facet : (Y.cycle.complex.cell tau).dimension = Y.cycle.dimension)
    (t : Fin m → Kˣ) (_interior : weightVector t ∈ intrinsicInterior ℝ
      (Y.cycle.complex.cell tau).carrier)
    (_generic : GenericTargetPoint P A m I phi (weightVector t)) :
    letI := Y.initialNoetherian t
    genericDegree P m I phi _finite * tropicalMultiplicity I t =
      indexSum P A F m I phi L (Y.cycle.complex.cell tau) (weightVector t)

end WantedExt.AlgebraicGeometry.GlobalSemistableSkeletonWanted
