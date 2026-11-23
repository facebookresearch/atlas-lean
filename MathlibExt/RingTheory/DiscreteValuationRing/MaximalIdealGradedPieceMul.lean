/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Trace.Defs
public import MathlibExt.RingTheory.DiscreteValuationRing.MaximalIdealGradedPiece

/-!
# Residue-field multiplication on maximal-ideal graded pieces

Let `R` be a discrete valuation ring with maximal ideal `𝔪` and residue field
`κ = R ⧸ 𝔪`. This file equips every graded piece `𝔪 ^ i ⧸ 𝔪 ^ (i + 1)` with
multiplication by a residue-field scalar, as a `κ`-linear endomorphism, together
with the representative formula showing it acts as representative
multiplication on the quotient.

This module is a prerequisite stage for the corrected ATLAS NumberTheoryI N261
upper different-exponent bound (Theorem 12.27), not the full N261 target. It
proves the multiplication definition, the representative formula, the
base-change conjugacy statement, and the graded-piece trace statement; the
quotient filtered-trace theorem, the different-ideal containment, either
valuation bound, and the tame equality remain deferred.

ATLAS source: [`v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean`, lines
1237--1324, at revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean#L1237-L1324).
Those lines define the ramification/different valuations and state the target
bounds, but they do not state the graded-piece multiplication proved here.

Source-to-API map: `residueFieldMulMaximalIdealGradedPiece`,
`residueFieldMulMaximalIdealGradedPiece_residue_mk`,
`residueFieldLinearEquivMaximalIdealGradedPiece_conj_lmul`, and
`trace_residueFieldMulMaximalIdealGradedPiece` are new supporting API for a
future maximal-ideal-filtration proof of the trace/different estimate; the
quotient filtered-trace theorem, the different containment, the valuation
bounds, and the tame-equality characterization remain deferred.

## Main results

* `IsDiscreteValuationRing.residueFieldMulMaximalIdealGradedPiece`:
  multiplication by a residue-field scalar as a `κ`-linear endomorphism of the
  `i`-th graded piece.
* `IsDiscreteValuationRing.residueFieldMulMaximalIdealGradedPiece_residue_mk`:
  multiplication by `residue x` acts on a quotient representative as the
  representative `R`-scalar action `x • ·`.
* `IsDiscreteValuationRing.residueFieldLinearEquivMaximalIdealGradedPiece_conj_lmul`:
  after restricting scalars to a base field `K`, the graded-piece equivalence
  conjugates residue-field left multiplication to the graded-piece
  multiplication endomorphism.
* `IsDiscreteValuationRing.trace_residueFieldMulMaximalIdealGradedPiece`:
  after restricting scalars to a base field `K`, the linear trace of the
  graded-piece multiplication endomorphism equals the algebra trace of the
  residue scalar.
-/

@[expose] public section

namespace IsDiscreteValuationRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **Multiplication by a residue class on a graded piece.** Let $R$ be a discrete valuation ring
with maximal ideal $\mathfrak{m}$ and residue field $\kappa = R/\mathfrak{m}$. For $a \in \kappa$
and $i \in \mathbb{N}$, this is the $\kappa$-linear endomorphism $x \mapsto a x$ of the graded
piece $\mathfrak{m}^i/\mathfrak{m}^{i+1}$. -/
noncomputable def residueFieldMulMaximalIdealGradedPiece
    (a : IsLocalRing.ResidueField R) (i : ℕ) :
    Module.End (IsLocalRing.ResidueField R) (MaximalIdealGradedPiece R i) :=
  LinearMap.lsmul _ _ a

/-- **Multiplication by a residue class on representatives.** Let $R$ be a discrete valuation
ring with maximal ideal $\mathfrak{m}$ and residue field $\kappa = R/\mathfrak{m}$. For $x \in R$,
$i \in \mathbb{N}$ and $y \in \mathfrak{m}^i$, multiplication by the residue class
$\bar{x} \in \kappa$ on $\mathfrak{m}^i/\mathfrak{m}^{i+1}$ sends the class of $y$ to the class
of $x y$. -/
@[simp]
theorem residueFieldMulMaximalIdealGradedPiece_residue_mk
    (x : R) (i : ℕ) (y : ((IsLocalRing.maximalIdeal R) ^ i : Ideal R)) :
    residueFieldMulMaximalIdealGradedPiece R (IsLocalRing.residue R x) i
        (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x • y) := by
  simp only [residueFieldMulMaximalIdealGradedPiece, LinearMap.lsmul_apply]
  exact Module.Quotient.mk_smul_mk _ _ x y

/-- **The residue-field isomorphism intertwines multiplication.** Let $R$ be a discrete valuation
ring with maximal ideal $\mathfrak{m}$ and residue field $\kappa = R/\mathfrak{m}$, let
$i \in \mathbb{N}$, and let $e : \kappa \to \mathfrak{m}^i/\mathfrak{m}^{i+1}$ be the
$\kappa$-linear isomorphism of the residue field with the graded piece. Let $K$ be a field, with
a $K$-algebra structure on $\kappa$ and a $K$-module structure on
$\mathfrak{m}^i/\mathfrak{m}^{i+1}$ such that $(c b) x = c (b x)$ for all $c \in K$,
$b \in \kappa$ and $x \in \mathfrak{m}^i/\mathfrak{m}^{i+1}$. Then for every $a \in \kappa$,
writing $\mu_a : \kappa \to \kappa$ for multiplication by $a$, the $K$-linear map
$e \circ \mu_a \circ e^{-1}$ equals multiplication by $a$ on $\mathfrak{m}^i/\mathfrak{m}^{i+1}$,
viewed as a $K$-linear map. -/
theorem residueFieldLinearEquivMaximalIdealGradedPiece_conj_lmul
    {K : Type*} [Field K] [Algebra K (IsLocalRing.ResidueField R)]
    (i : ℕ) [Module K (MaximalIdealGradedPiece R i)]
    [IsScalarTower K (IsLocalRing.ResidueField R) (MaximalIdealGradedPiece R i)]
    (a : IsLocalRing.ResidueField R) :
    ((residueFieldLinearEquivMaximalIdealGradedPiece R i).restrictScalars K).conj
        (Algebra.lmul K (IsLocalRing.ResidueField R) a) =
      (residueFieldMulMaximalIdealGradedPiece R a i).restrictScalars K := by
  refine LinearMap.ext fun y => ?_
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.restrictScalars_apply,
    LinearEquiv.restrictScalars_symm_apply, Algebra.coe_lmul_eq_mul,
    LinearMap.mul_apply', LinearMap.restrictScalars_apply,
    residueFieldMulMaximalIdealGradedPiece, LinearMap.lsmul_apply]
  rw [← smul_eq_mul, map_smul, LinearEquiv.apply_symm_apply]

/-- **Trace of multiplication on a graded piece.** Let $R$ be a discrete valuation ring with
maximal ideal $\mathfrak{m}$ and residue field $\kappa = R/\mathfrak{m}$, let $i \in \mathbb{N}$,
and let $K$ be a field, with a $K$-algebra structure on $\kappa$ and a $K$-module structure on
$\mathfrak{m}^i/\mathfrak{m}^{i+1}$ such that $(c b) x = c (b x)$ for all $c \in K$,
$b \in \kappa$ and $x \in \mathfrak{m}^i/\mathfrak{m}^{i+1}$. Then for every $a \in \kappa$, the
trace of multiplication by $a$ on $\mathfrak{m}^i/\mathfrak{m}^{i+1}$, as a $K$-linear map,
equals the trace $\operatorname{Tr}_{\kappa/K}(a)$.

Each trace is taken to be $0$ when the corresponding space is not finite-dimensional over $K$. -/
theorem trace_residueFieldMulMaximalIdealGradedPiece
    {K : Type*} [Field K] [Algebra K (IsLocalRing.ResidueField R)]
    (i : ℕ) [Module K (MaximalIdealGradedPiece R i)]
    [IsScalarTower K (IsLocalRing.ResidueField R) (MaximalIdealGradedPiece R i)]
    (a : IsLocalRing.ResidueField R) :
    LinearMap.trace K (MaximalIdealGradedPiece R i)
        ((residueFieldMulMaximalIdealGradedPiece R a i).restrictScalars K) =
      Algebra.trace K (IsLocalRing.ResidueField R) a := by
  rw [Algebra.trace_apply, ← LinearMap.trace_conj'
    (Algebra.lmul K (IsLocalRing.ResidueField R) a)
    ((residueFieldLinearEquivMaximalIdealGradedPiece R i).restrictScalars K),
    residueFieldLinearEquivMaximalIdealGradedPiece_conj_lmul]

end IsDiscreteValuationRing
