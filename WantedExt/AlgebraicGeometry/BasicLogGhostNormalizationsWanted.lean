/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.BasicLogGhostNormalizations

/-!
# Geometric basicization and all stalk/base-change normalization requests

The source uses actual characteristic stalks, actual component/node
enumerations, ordered native site-point generizations, the computed
contact b−a, the genuine saturated relation quotient, and the actual
initial basic family on the same ordinary stable map.

The geometric constructor retains the primary source's characteristic-zero
finite-type scope and Zariski-defined fs target/base log charts. The public
types and actual specialization/base-change operations are independent
of a choice of coefficient field. No basicness or quotient-equivalence
conclusion is an input to the constructor.

Reference: Gross–Siebert arXiv:1102.4322v2, equations1.7/1.8,
Construction1.16, equation1.14, Definition1.20, Lemma1.23,
Proposition1.24 and diagram1.16.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.BasicLogGhostNormalizations

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams GeometricLogGhosts
open BasicLogMapFamilies BasicLogGeometricGhosts BasicLogGhostNormalizations

/-- Generic geometric field-extension integration, fixed on every native
small-étale lift and log-section generator. -/
public def_wanted fieldExtensionGhostComparison [InverseImageTheory.{0}]
    (Y : LogScheme.{0}) (K L : Type) [Field K] [IsSepClosed K] [Field L] [IsSepClosed L]
    (f : K →+* L) (x : Spec (.of K) ⟶ Y.scheme) (y : Spec (.of L) ⟶ Y.scheme)
    (h : Spec.map (CommRingCat.ofHom f) ≫ x = y) : FieldGhostComparison Y f x y h

/-- Basicization of stable log maps (Gross–Siebert, arXiv:1102.4322, Construction 1.16 and
Proposition 1.24): let $k$ be a field of characteristic zero, $X \to S$ a morphism of fine saturated
log schemes with Zariski fine saturated charts whose underlying morphism is of finite type, with $S$
of finite type over $k$, and $M$ a stable log map of genus $g$ with $n$ marked points over a
Noetherian scheme $W$ of finite type over $S$ (log structures being on small étale sites, where
sheaves of commutative monoids are assumed to have inverse images along every morphism of
schemes, `InverseImageTheory`). Then $M$ has a basicization: a log enhancement of the same
underlying stable map that is initial among enhancements and universally minimal
(`Basicization`); and at every geometric point $t : \operatorname{Spec} K \to W$, with $K$
algebraically closed, there are a fibre type $H$ of $M$ at $t$ and an identification of the ghost
stalk of the basicization at $t$ with the basic monoid of the contact diagram of $H$
(`BasicGhostModel`). -/
public def_wanted geometricBasicization [InverseImageTheory.{0}]
    (k : Type) [Field k] [CharZero k]
    (X S : LogScheme.{0}) (hX : X.IsFineSaturated) (hS : S.IsFineSaturated)
    (hXZariski : HasZariskiFineSaturatedCharts X) (hSZariski : HasZariskiFineSaturatedCharts S)
    (q : EtaleLogSchemes.Hom X S) [LocallyOfFiniteType q.map] [QuasiCompact q.map]
    (c : S.scheme ⟶ Spec (.of k)) [LocallyOfFiniteType c] [QuasiCompact c]
    (n g : ℕ) (W : Scheme.{0}) [IsNoetherian W]
    (b : W ⟶ S.scheme) [LocallyOfFiniteType b] [QuasiCompact b]
    (M : StableLogMap q n g W b) :
    Σ' B : Basicization M,
      ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ W),
        Σ H : FibreType M t, BasicGhostModel M B t H

/-- Base change of basicizations: for a morphism $h : W' \to W$ of schemes over $S$, stable log maps
$M$ over $W$ and $M'$ over $W'$ of genus $g$ with $n$ marked points to $q : X \to S$ (log
structures being on small étale sites, where sheaves of commutative monoids are assumed to have
inverse images along every morphism of schemes, `InverseImageTheory`), a Cartesian square $C$
exhibiting the marked curve of $M'$, with its map to $X$, as the pullback of that of $M$ along $h$,
a log base change $A$ from $M'$ to $M$ over $C$ (`LogBaseChange`: strict log morphisms of the
bases and of the curves over $h$ and $C$, compatible with the projections and with the log maps to
$X$ and to $S$), and basicizations $B$ and $B'$ of $M$ and $M'$: a log base change from the
basicization $B'$ to $B$ over the same square $C$ (`change`), compatible with $A$ through the
comparison maps from the basic log structures to those of $M$ and $M'$, on the bases
(`base_comparison`) and on the curves (`curve_comparison`). -/
public def_wanted basicizationBaseChange [InverseImageTheory.{0}]
    (X S : LogScheme.{0}) (q : EtaleLogSchemes.Hom X S)
    (n g : ℕ) (W W' : Scheme.{0}) (b : W ⟶ S.scheme) (h : W' ⟶ W)
    (M : StableLogMap q n g W b) (M' : StableLogMap q n g W' (h ≫ b))
    (C : GeneralStableMapFamilies.BaseChangeData M.family h M'.family)
    (A : LogBaseChange M h M' C) (B : Basicization M) (B' : Basicization M') :
    BasicizedBaseChange M B h M' C B' A

end WantedExt.AlgebraicGeometry.BasicLogGhostNormalizations
