/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GeneralSchubertClasses

/-!
# Source-normalized all-rank flag and Schubert construction targets

Brion, math/0410240v1, sections 1.1–1.4, 2.2 and Theorem 3.1.2.
Representability is on actual nested native Grassmannian submodules over
every complex algebra. Rank ideals, partial maps, native flag towers,
weight-frame transitions, Chern/cycle expressions and the schematic graph
closure are fixed in MathlibExt. The requests build their producers and
prove direct formulas; none assumes the corresponding Schubert conclusion.
The equality at both projective boundary points is an equality of actual
ideal sheaves, hence of the native associated subschemes.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.GeneralSchubertGeometryWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open GeneralFlagSchemes SchubertRankSchemes BottSamelsonFlagSchemes
open SchubertDiagonalFamilies FlagWeightLineBundles GeneralSchubertClasses
open PerverseSheaves ComplexAnalytification CompactSupportBetti ProperBettiFunctoriality
open AlgebraicBundleGeometry BettiCycleRealization BettiCharacteristicClasses

def_wanted flag_scheme (n : ℕ) (ranks : Shape n) : FlagSchemeModel n ranks

def_wanted partial_projection {n : ℕ} {D E : Shape n}
    (F : FlagSchemeModel n D) (Q : FlagSchemeModel n E) (h : E ⊆ D) : ForgetMap F Q h

def_wanted coordinate_points (n : ℕ) (F : FlagSchemeModel n (fullShape n)) : CoordinatePoints n F

def_wanted schubert_ideal {n : ℕ} {ranks : Shape n} (F : FlagSchemeModel n ranks)
    (w : Equiv.Perm (Fin n)) (opposite : Bool) : SchubertIdealModel F w opposite

def_wanted adjacent_projections (n : ℕ) (F : FlagSchemeModel n (fullShape n)) : FlagProjections n F

theorem_wanted bott_samelson_resolution {n : ℕ} (F : FlagSchemeModel n (fullShape n))
    (C : CoordinatePoints n F) (P : FlagProjections n F) (word : List (SimpleRoot n))
    (_reduced : IsReducedWord word) (S : SchubertIdealModel F (wordPermutation word) false) :
    ResolutionProperties C P word S

def_wanted weight_line {n : ℕ} (F : FlagSchemeModel n (fullShape n)) (weight : Fin n → ℤ) :
    WeightLine F weight

def_wanted diagonal_translation {n : ℕ} (F : FlagSchemeModel n (fullShape n)) (a : Fin n → ℤ) :
    Translation F a

theorem_wanted projective_line_charts : ProjectiveLineChartProofs

theorem_wanted schubert_is_variety {n : ℕ} {ranks : Shape n} (F : FlagSchemeModel n ranks)
    (w : Equiv.Perm (Fin n)) (side : Bool) (S : SchubertIdealModel F w side) :
    IsComplexVariety S.scheme

theorem_wanted diagonal_boundary {n : ℕ} (F : FlagSchemeModel n (fullShape n))
    (C : ProjectiveLineChartProofs) (a : Fin n → ℤ) (_decreasing : StrictAnti a)
    (T : Translation F a) (S : ∀ w : Equiv.Perm (Fin n), SchubertIdealModel F w false)
    (O : ∀ w : Equiv.Perm (Fin n), SchubertIdealModel F w true) (infinity : Bool) :
    projectiveBoundaryIdeal C T infinity = schubertUnionIdeal S O infinity

theorem_wanted chevalley
    (D : ∀ (X : ComplexScheme) [IsComplexVariety X], DualizingComplex (space X))
    (P : ∀ {X Y : ComplexScheme} [IsComplexVariety X] [IsComplexVariety Y]
      (f : X ⟶ Y) [IsProper f.left], ProperPullback (spaceMap f))
    (C : CycleMap D P) (T : CharacteristicClassTheory D P)
    (_samePurity : ∀ (X : ComplexScheme) [IsComplexVariety X] (d : ℕ)
      [SmoothOfRelativeDimension d X.hom] [IsProper X.hom]
      (hX : ProjectiveSpace.IsProjective X),
      C.purity X d hX = T.family.iso X d)
    {n : ℕ} (F : FlagSchemeModel n (fullShape n))
    (S : ∀ w : Equiv.Perm (Fin n), SchubertIdealModel F w false)
    [∀ w, IsNoetherian (S w).scheme.left] (weight : Fin n → ℤ) (L : WeightLine F weight)
    (B : ProjectiveBundle F.scheme (flagDimension (fullShape n)) 0 L.object)
    (V : LineTotalSpace B.total (flagDimension (fullShape n)) B.tautological)
    (w : Equiv.Perm (Fin n)) :
    cohomologyCast (by omega)
      (BettiRealization.cup (space F.scheme)
        (weightChern D P F T.toProjectiveBundleTheory weight L B V)
        (schubertClass D P C F w (S w))) = chevalleySum D P C F S weight w

end WantedExt.AlgebraicGeometry.GeneralSchubertGeometryWanted
