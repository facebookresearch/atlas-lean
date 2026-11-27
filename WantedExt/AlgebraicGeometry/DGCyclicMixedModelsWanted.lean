/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Algebra.Homology.DGCyclicMixedModels

/-!
# Wanted DG Hochschild and Connes assembly

Construct the fixed direct-sum total and its computed degree -1 Connes
operator. Every term and map is already specified publicly. No Hodge
degeneration, smooth-diagonal or Calabi--Yau theorem is an input.

Sources: Kaledin, arXiv:math/0611623v4, §1.3; Loday, §1.1. The
ungraded TauCeti Connes cochain proofs are credited as background in the
public module, with their distinct cochain-versus-chain scope explicit.
-/

namespace WantedExt.AlgebraicGeometry.DGCyclicMixedModelsWanted

open MathlibExt.Algebra.Homology.DGCyclicBarModels
open MathlibExt.Algebra.Homology.DGCyclicMixedModels

universe u

/-- **The Hochschild mixed complex of a DG algebra.** For a commutative ring $k$ and a DG algebra
$A$ over $k$: a cochain complex $C$ whose degree-$r$ term is identified with
$\bigoplus_{n \ge 0} (A^{\otimes (n+1)})^{r+n}$, with differential $(-1)^n d$ (the internal
differential of $A^{\otimes (n+1)}$) plus the alternating sum $\sum_i (-1)^i d_i$ of the bar faces,
together with a cochain $B$ of degree $-1$ on $C$ satisfying $dB + Bd = 0$ and $B^2 = 0$, given on
the summands by Connes' operator $(1 - t)\,s\,N$, where $t = (-1)^n \tau$ is the signed cyclic
rotation, $N = 1 + t + \dots + t^n$ and $s$ inserts the unit in front
(`HochschildMixedModel A`). -/
def_wanted dg_hochschild_mixed_model (k : Type u) [CommRing k] (A : DGAlgebra k) :
  HochschildMixedModel A

end WantedExt.AlgebraicGeometry.DGCyclicMixedModelsWanted
