/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.FanoKSemistabilityFamilies

@[expose] public noncomputable section

/-!
# K-semistability is open in actual smooth projective Fano families

Authors: Harold Blum, Yuchen Liu, Chenyang Xu; Kento Fujita; Chi Li.
Sources: Blum--Liu--Xu, Openness of K-semistability for Fano varieties,
Corollary 1.2 and Definition--Theorem 2.6,
https://arxiv.org/abs/1907.02408;
Fujita, A valuative criterion for uniform K-stability of Q-Fano varieties,
Definition 1.1 and Corollary 1.5(2), https://arxiv.org/abs/1602.00901.

The predicate uses the actual prime-divisor local DVR, the canonical
top-Kähler Jacobian order, actual anticanonical H0 ideal-adic spaces and
ENNReal volume integrals. The nonzero Jacobian has finite order and the
actual Hilbert leading coefficient fixes a finite positive volume.
No DF, valuation-volume or beta oracle, test-configuration carrier,
moduli constructor or Kähler--Einstein existence assumption is used.
The retained scope is the smooth complex Fano-family specialization;
general singular log Fano moduli and metric equivalences remain separate.
-/

namespace WantedExt.AlgebraicGeometry.FanoKSemistabilityOpenness

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.FanoKSemistabilityFamilies

/-- Blum--Liu--Xu openness for the actual valuative semistability criterion
in a genuine smooth projective family of positive-dimensional complex Fano varieties. -/
public theorem_wanted smoothFano_kSemistable_locus_open
    (n : ℕ) (positiveDimension : 0 < n) (F : SmoothFanoFamily n) :
    ∃ U : F.B.left.Opens, ∀ b : RationalPoint F.B,
      parameterPoint F b ∈ U ↔ SemistableFiber F b

end WantedExt.AlgebraicGeometry.FanoKSemistabilityOpenness
