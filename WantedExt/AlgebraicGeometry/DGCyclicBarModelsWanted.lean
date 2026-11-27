/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Algebra.Homology.DGCyclicBarModels

/-!
# Wanted assembly of the source-normalized DG cyclic bar

The input is an actual cochain monoid. The output is normalized on all
tensor-power terms, actual multiplication faces and actual unit
degeneracies. No degeneration or cyclic-homology comparison is an input.

Sources: Loday, Cyclic homology, §1.1; Kaledin,
arXiv:math/0611623v4, §1.3. Generic cochain tensor and braiding proofs are
already completed in MathlibExt.CategoryTheory.DGSource.
-/

namespace WantedExt.AlgebraicGeometry.DGCyclicBarModelsWanted

open MathlibExt.Algebra.Homology.DGCyclicBarModels

universe u

/-- **The cyclic bar construction of a DG algebra.** For a commutative ring $k$ and a DG algebra
$A$ over $k$ (a monoid in cochain complexes of $k$-modules): a simplicial cochain complex whose
term in degree $n$ is identified with $A^{\otimes (n+1)}$, under which, counting factors from
$0$, the faces $d_0, \dots, d_{n+1}$ from degree $n + 1$ to degree $n$ are: $d_i$ for $i \le n$
multiplies the factors $i$ and $i + 1$, and $d_{n+1}$ first moves the last factor to the front by
the Koszul-signed braiding and then multiplies the first two factors; the degeneracy $s_i$
($i \le n$) from degree $n$ to degree $n + 1$ inserts the unit after the factor $i$
(`CyclicBarModel A`). -/
def_wanted dg_cyclic_bar_model (k : Type u) [CommRing k] (A : DGAlgebra k) :
  CyclicBarModel A

end WantedExt.AlgebraicGeometry.DGCyclicBarModelsWanted
