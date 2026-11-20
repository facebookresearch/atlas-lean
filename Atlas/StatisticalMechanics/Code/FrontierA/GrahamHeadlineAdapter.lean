/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamAgreementVBGInhomogeneous















open SimpleGraph

namespace StatMech.FrontierA

open StatMech.Ising
open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



theorem grahamStrengthenedGHS_inhomogeneous
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    (i j k : V) :
    ghsiUrsell3 G K hf i j k <=
      -2 * ghsiCovariance G K hf i k *
        ghsiCovariance G K hf j k * grahamInhomOne G K hf k :=
  grahamImprovedGHS_inhomogeneous G K hf hK hhf i j k



theorem grahamStrengthenedGHS_homogeneous
    (beta h : Real) (hbeta : 0 <= beta) (hh : 0 <= h)
    (i j k : V) :
    eg_ursell3 G beta h i j k <=
      -2 * cov2 G beta h i k * cov2 G beta h j k *
        onePt G beta h k :=
  grahamImprovedGHS_agreement G beta h hbeta hh i j k

end StatMech.FrontierA
