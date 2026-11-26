/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FramedMeromorphicGroupModels
public import MathlibExt.AlgebraicGeometry.ReductiveGroupSchemeModels
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Uniqueness of the finite-pole G-factorization

Two factorizations of a meromorphic modification through `𝒪(Q)[1/t]`
restrict to the same punctured comparison element by their normalizations.
Since `G` is affine over `Spec E`, its points are determined by their
global sections, and restriction along the injective finite-pole map is
injective on those sections.

Source: Fargues--Scholze, arXiv:2102.13459v4, Section III.3 and VI.1;
Beauville--Laszlo, *Un lemme de descente*.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MeromorphicGroupFactorization

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicCoefficientCompletion
open FramedMeromorphicGroupModels

/-- Global sections of a spectrum map along an injective ring map are injective. -/
private theorem specMap_appTop_injective
    (R S : CommRingCat) (j : R ⟶ S) (hj : Function.Injective j.hom) :
    Function.Injective (Spec.map j).appTop.hom := by
  intro x y hxy
  have hnat := congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality j)
  have hx : (Scheme.ΓSpecIso S).hom.hom (((Spec.map j).appTop).hom x) =
      j.hom ((Scheme.ΓSpecIso R).hom.hom x) :=
    DFunLike.congr_fun hnat x
  have hy : (Scheme.ΓSpecIso S).hom.hom (((Spec.map j).appTop).hom y) =
      j.hom ((Scheme.ΓSpecIso R).hom.hom y) :=
    DFunLike.congr_fun hnat y
  have hmid : j.hom ((Scheme.ΓSpecIso R).hom.hom x) =
      j.hom ((Scheme.ΓSpecIso R).hom.hom y) := by
    rw [← hx, ← hy, hxy]
  have hbase : (Scheme.ΓSpecIso R).hom.hom x = (Scheme.ΓSpecIso R).hom.hom y :=
    hj hmid
  have hInv : Function.HasLeftInverse (Scheme.ΓSpecIso R).hom.hom :=
    ⟨(Scheme.ΓSpecIso R).inv.hom, fun x =>
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
        (Iso.hom_inv_id (Scheme.ΓSpecIso R))) x⟩
  exact Function.HasLeftInverse.injective hInv hbase

/-- Two `G`-points over the finite-pole ring that agree after injective restriction agree. -/
private theorem overPoint_unique
    (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    [ReductiveGroupSchemeModels.IsReductive (Spec (.of E)) G]
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U)
    (h : IsUnit (sectionMap p E Q.puncture.map Q.parameter))
    (hi : Function.Injective (puncturedMap p E d U Q h))
    (a b : (AlgebraicGroupPointRepresentations.testSchemes E).obj
      (op (meromorphicTest p E d U Q)) ⟶ G)
    (hcomp : (AlgebraicGroupPointRepresentations.testSchemes E).map
          (punctureTestMap p E d U Q h).op ≫ a =
        (AlgebraicGroupPointRepresentations.testSchemes E).map
          (punctureTestMap p E d U Q h).op ≫ b) :
    a = b := by
  have hleft :
      ((AlgebraicGroupPointRepresentations.testSchemes E).map
        (punctureTestMap p E d U Q h).op).left ≫ a.left =
      ((AlgebraicGroupPointRepresentations.testSchemes E).map
        (punctureTestMap p E d U Q h).op).left ≫ b.left :=
    congrArg Over.Hom.left hcomp
  have happTop : a.left.appTop ≫
      ((AlgebraicGroupPointRepresentations.testSchemes E).map
        (punctureTestMap p E d U Q h).op).left.appTop =
      b.left.appTop ≫
        ((AlgebraicGroupPointRepresentations.testSchemes E).map
          (punctureTestMap p E d U Q h).op).left.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
    exact congrArg Scheme.Hom.appTop hleft
  have hinj : Function.Injective
      (((AlgebraicGroupPointRepresentations.testSchemes E).map
        (punctureTestMap p E d U Q h).op).left.appTop.hom) :=
    specMap_appTop_injective _ _ (CommRingCat.ofHom (puncturedMap p E d U Q h)) hi
  have happTopEq : a.left.appTop = b.left.appTop := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    apply hinj
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom happTop) x
  have hAff : IsAffine G.left := AlgebraicGeometry.isAffine_of_isAffineHom G.hom
  have hEq : a.left = b.left :=
    AlgebraicGeometry.ext_of_isAffine happTopEq
  exact Over.OverMorphism.ext hEq

/-- Uniqueness of the finite-pole factorization: let $p$ be a prime, $E$ a field and $G$ a
reductive group scheme over $E$, with given torsor descent data $H$ and pullback compatibility $P$
on analytic adic spaces over $E$. Let $d : D → X$ be a morphism of such spaces with a puncture
$U$, and $Q$ a pole chart of $d$ whose parameter $t$ restricts to a unit on the punctured chart,
such that restriction from $\mathcal{O}(Q)[1/t]$ to the sections of the punctured chart is
injective. For every modification $M$ of $G$-bundles on $X$ along $d$ (`Modification`) with
integral frames of both of its bundles on $Q$, any two factorizations of $M$ through
$\mathcal{O}(Q)[1/t]$ (`GroupFactorization`) have the same point of $G$. -/
public theorem meromorphicGroupFactorization_unique
    (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    [ReductiveGroupSchemeModels.IsReductive (Spec (.of E)) G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U)
    (h : IsUnit (sectionMap p E Q.puncture.map Q.parameter))
    (hi : Function.Injective (puncturedMap p E d U Q h))
    (M : Modification p E G H P d U)
    (left : IntegralFrame p E G H d U Q M.left)
    (right : IntegralFrame p E G H d U Q M.right)
    (F N : GroupFactorization p E G H P d U Q h M left right) : F.element = N.element := by
  have hmap := F.normalized.trans N.normalized.symm
  have hcomp :
      (AlgebraicGroupPointRepresentations.testSchemes E).map
          (punctureTestMap p E d U Q h).op ≫ F.element =
        (AlgebraicGroupPointRepresentations.testSchemes E).map
          (punctureTestMap p E d U Q h).op ≫ N.element := hmap
  exact overPoint_unique p E G d U Q h hi F.element N.element hcomp

end WantedExt.AlgebraicGeometry.MeromorphicGroupFactorization
