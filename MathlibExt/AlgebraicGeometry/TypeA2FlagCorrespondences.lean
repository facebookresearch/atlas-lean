/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.HermitianFlags
public import MathlibExt.AlgebraicGeometry.BettiGysin
public import MathlibExt.AlgebraicGeometry.BettiCycleRealization

/-!
# Literal type A2 flag and Bott--Samelson correspondences

The flag manifold is the matrix-projector model with its actual Euclidean
subspace topology. A simple correspondence consists of pairs equal away
from the specified line or plane. Bott--Samelson galleries are actual finite
sequences of such adjacent flags, starting at the explicit standard flag.

Demazure operators are computed by the actual inverse-image map followed
by proper duality trace. The carrier is the existing rational derived-sheaf
cohomology and the degree is exactly minus two. Compatible purity choices
and geometric nil-Hecke laws are a separate construction target. The point
class is itself the actual proper trace of the standard geometric point.

Reference: Bernstein--Gelfand--Gelfand, *Schubert cells and the cohomology of
the spaces G/P*, Russian Math. Surveys 28 (1973), §3; Bott--Samelson,
*Applications of the theory of Morse to symmetric spaces* (1958).
TauCeti's `Geometry/Symplectic/BottSamelson/FixedMoment.lean` at revision
62bbc0596dc3539d488232e4e924a338548ea0a9 computes eight moment values and
their convex hull. Those completed numerical/combinatorial facts are
excluded; no construction of these correspondences is inferred from them.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.TypeA2FlagCorrespondences

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.LinearAlgebra.HermitianFlags
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.BettiRealization
open MathlibExt.AlgebraicGeometry.CompactSupportBetti
open MathlibExt.AlgebraicGeometry.ProperBettiFunctoriality
open MathlibExt.AlgebraicGeometry.BettiFunctoriality
open MathlibExt.AlgebraicGeometry.BettiGysin

attribute [local instance] HasDerivedCategory.standard

/-- The line index 1 or plane index 2 of an actual flag. -/
def simpleIndex (i : Fin 2) : Fin 4 := ⟨i.val + 1, by omega⟩

def Adjacent (i : Fin 2) (F G : Flag 3) : Prop :=
  ∀ j : Fin 4, j ≠ simpleIndex i → F.val j = G.val j

abbrev Correspondence (i : Fin 2) := {p : Flag 3 × Flag 3 // Adjacent i p.1 p.2}
abbrev correspondenceSpace (i : Fin 2) : TopCat.{0} := TopCat.of (Correspondence i)

def firstProjection (i : Fin 2) : correspondenceSpace i ⟶ flagSpace 3 :=
  TopCat.ofHom ⟨fun p => p.val.1, continuous_fst.comp continuous_subtype_val⟩

def secondProjection (i : Fin 2) : correspondenceSpace i ⟶ flagSpace 3 :=
  TopCat.ofHom ⟨fun p => p.val.2, continuous_snd.comp continuous_subtype_val⟩

abbrev Gallery (w : List (Fin 2)) :=
  {F : Fin (w.length + 1) → Flag 3 // F 0 = standardFlag ∧
    ∀ k : Fin w.length, Adjacent (w.get k)
      (F ⟨k.val, by omega⟩) (F ⟨k.val + 1, by omega⟩)}

abbrev gallerySpace (w : List (Fin 2)) : TopCat.{0} := TopCat.of (Gallery w)

def galleryEvaluation (w : List (Fin 2)) : gallerySpace w ⟶ flagSpace 3 :=
  TopCat.ofHom ⟨fun F => F.val (Fin.last w.length),
    (continuous_apply (Fin.last w.length)).comp continuous_subtype_val⟩

abbrev pointSpace : TopCat.{0} := TopCat.of PUnit

def standardPoint : pointSpace ⟶ flagSpace 3 :=
  TopCat.ofHom ⟨fun _ => standardFlag, continuous_const⟩

/-- Standing actual compact-support duality representations and proper
pullback/trace data, already characterized by the completed support. -/
structure DualityInputs where
  flag : DualizingComplex (flagSpace 3)
  correspondence : ∀ i : Fin 2, DualizingComplex (correspondenceSpace i)
  point : DualizingComplex pointSpace
  projection : ∀ i : Fin 2, ProperPullback (firstProjection i)
  pointMap : ProperPullback standardPoint

/-- Purity isomorphisms for the dualizing complexes `U` of the type $A_2$ flag correspondences:
isomorphisms identifying the dualizing complex of the space of complete flags in $\mathbb{C}^3$ with
$\mathbb{Q}[6]$ (the constant sheaf $\mathbb{Q}$ shifted by $6$), the dualizing complex of each of
the two simple correspondences (pairs of flags that agree except in the line, or except in the
plane) with $\mathbb{Q}[8]$, and the dualizing complex of the point with $\mathbb{Q}[0]$. No
compatibility between these isomorphisms is required. -/
structure Purities (U : DualityInputs) where
  flag : U.flag.obj ≅ (rationalUnit (flagSpace 3))⟦(6 : ℤ)⟧
  correspondence : ∀ i : Fin 2,
    (U.correspondence i).obj ≅ (rationalUnit (correspondenceSpace i))⟦(8 : ℤ)⟧
  point : U.point.obj ≅ (rationalUnit pointSpace)⟦(0 : ℤ)⟧

variable (U : DualityInputs) (O : Purities U)

def demazure (i : Fin 2) (n : ℤ) :
    BettiRealization.Cohomology (flagSpace 3) n →ₗ[ℚ]
      BettiRealization.Cohomology (flagSpace 3) (n - 2) :=
  BettiCycleRealization.cohomologyCast (by omega) ∘ₗ
    cohomologyPushforward (U.projection i) (U.correspondence i) U.flag 4 3
      (O.correspondence i) O.flag n ∘ₗ cohomologyPullback (secondProjection i) n

def pointClass : BettiRealization.Cohomology (flagSpace 3) 6 :=
  cohomologyPushforward U.pointMap U.point U.flag 0 3 O.point O.flag 0 (unitClass pointSpace)

/-- The remaining result chooses purities for the fixed operators and
proves their geometric laws. No Demazure operator is provided as a field. -/
structure NilHeckePurities (U : DualityInputs) extends Purities U where
  square_zero : ∀ (i : Fin 2) (n : ℤ),
    demazure U toPurities i (n - 2) ∘ₗ demazure U toPurities i n = 0
  braid : ∀ n : ℤ,
    demazure U toPurities 0 (n - 2 - 2) ∘ₗ demazure U toPurities 1 (n - 2) ∘ₗ
      demazure U toPurities 0 n =
    demazure U toPurities 1 (n - 2 - 2) ∘ₗ demazure U toPurities 0 (n - 2) ∘ₗ
      demazure U toPurities 1 n
  point_normalization :
    demazure U toPurities 0 2 (demazure U toPurities 1 4
      (demazure U toPurities 0 6 (pointClass U toPurities))) = unitClass (flagSpace 3)

end MathlibExt.AlgebraicGeometry.TypeA2FlagCorrespondences
