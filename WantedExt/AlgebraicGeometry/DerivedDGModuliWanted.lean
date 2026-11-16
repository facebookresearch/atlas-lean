/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DerivedDGModuli
public import MathlibExt.AlgebraicGeometry.DerivedOpenSubstacks
public import MathlibExt.AlgebraicGeometry.DerivedDGModuliTangentModels

/-!
# Wanted source-normalized DG moduli and local geometricity

The moduli functor is the completed literal resolution-Hom functor.
The requests construct its genuine Reedy frame, coherent coefficient
strictification and derived étale stack model. The source finite-type
predicate is a DG-algebra homotopical finite-presentation and enhanced
module-Morita test; geometricity is a conclusion.

Native module uncurrying and projective replacements already have
separate shared construction requests. A ModulePointModel uses those
actual outputs; no point's endomorphism or tangent complex is freely
named or assumed to equal the source formula.

References: Toën--Vaquié, arXiv:math/0503269v5, Definition2.4(7),
§3.1 pp36--37, Lemma3.1 and Theorem3.6; Hovey, Model Categories, §5.
-/

open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedStackFibreModels
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.DerivedOpenSubstacks
open MathlibExt.AlgebraicGeometry.SimplicialHomotopyLimits
open MathlibExt.AlgebraicGeometry.DerivedCotangentModels
open MathlibExt.AlgebraicGeometry.DerivedDGModuliTangentModels
open scoped Simplicial

universe u

/-- Construct the genuine augmented Reedy-cofibrant DG resolution, including latching maps. -/
def_wanted dg_cosimplicial_resolution (k : Type u) [CommRing k] (T : DGCat k) :
  DGFrame k T

/-- DG-algebra frames use the actual cochain-map and degreewise-surjective model tests. -/
def_wanted dg_algebra_cosimplicial_resolution (k : Type u) [CommRing k]
    (A : MathlibExt.Algebra.Homology.DGCyclicBarModels.DGAlgebra k) : AlgebraFrame k A

/-- Strictify the actual coefficient-perfect categories with normalized coherent scalar units. -/
def_wanted strict_perfect_scalar_system (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N) : StrictPerfectSystem N S

/-- The native source frame computes a Kan mapping space into a fibrant enhanced DG category. -/
theorem_wanted dg_cosimplicial_mapping_kan (k : Type u) [CommRing k]
    (T : DGCat k) (R : DGFrame k T) (D : LargeDGCategory k) :
  SSet.KanComplex (dgMapping R D)

/-- The actual perfect realization induces the native derived DG mapping-space comparison. -/
theorem_wanted dg_moduli_native_perfect_comparison (k : Type u) [CommRing k]
    (T : DGCat k) (R : DGFrame k (oppositeCategory T))
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (P : StrictPerfectSystem N S) (A : SAlg k) :
  WeakEquivalence (nativePerfComparison R P A)

/-- Assemble the exact computed M_T as a derived étale stack with its actual augmentation. -/
def_wanted dg_moduli_etale_stack_model (k : Type u) [CommRing k]
    (T : DGCat k) (R : DGFrame k (oppositeCategory T))
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (P : StrictPerfectSystem N S) (Q : AlgebraReplacementFunctor k) :
  ModuliStackModel R P Q

/-- The source finite-type DG category gives local geometricity and local finite presentation.
Open pieces may have different geometric levels; no uniform amplitude bound is imposed. -/
theorem_wanted finite_type_dg_moduli_locally_geometric (k : Type u) [CommRing k]
    (T : DGCat k) (hfinite : IsFiniteType T) (R : DGFrame k (oppositeCategory T))
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (P : StrictPerfectSystem N S) (Q : AlgebraReplacementFunctor k)
    (M : ModuliStackModel R P Q) :
  IsLocallyGeometric M.stack ∧ IsLocallyOfFinitePresentationStack M.stack

/-- Construct the cotangent from the actual point's split square-zero deformation tests. -/
def_wanted finite_type_dg_moduli_cotangent (k : Type u) [CommRing k]
    (T : DGCat k) (hfinite : IsFiniteType T) (R : DGFrame k (oppositeCategory T))
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (P : StrictPerfectSystem N S) (Q : AlgebraReplacementFunctor k)
    (M : ModuliStackModel R P Q)
    (E : ((moduliFunctor R P).obj (baseAlgebra k)) _⦋0⦌)
    (H : KanPathModel (M.stack.functor.obj (baseAlgebra k))) :
  CotangentRepresentation N M.stack.toDerivedPrestack (baseAlgebra k) (moduliPoint M E) H

/-- The independent deformation tangent identifies with the actual module RHom(E,E)[1].
The target uses a projective replacement over the full T-action enveloping category,
not the strict natural-transformation complex of objectwise perfect values. -/
def_wanted finite_type_dg_moduli_tangent_comparison (k : Type u) [CommRing k]
    (T : DGCat k) (hfinite : IsFiniteType T) (R : DGFrame k (oppositeCategory T))
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (P : StrictPerfectSystem N S) (Q : AlgebraReplacementFunctor k)
    (M : ModuliStackModel R P Q)
    (E : ((moduliFunctor R P).obj (baseAlgebra k)) _⦋0⦌)
    (H : KanPathModel (M.stack.functor.obj (baseAlgebra k)))
    (L : CotangentRepresentation N M.stack.toDerivedPrestack
      (baseAlgebra k) (moduliPoint M E) H)
    (D : ModulePointModel R P (baseAlgebra k) E) :
  (cochainQ k).obj (tangentComplex L) ≅
    (cochainQ k).obj ((derivedEndomorphisms D)⟦(1 : ℤ)⟧)
