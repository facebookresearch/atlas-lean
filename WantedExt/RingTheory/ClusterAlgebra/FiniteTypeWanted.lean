/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.RingTheory.ClusterAlgebra.LaurentPhenomenonWanted

/-!
# Finite type classification of cluster algebras (wanted)

Statement-only target from Fomin and Zelevinsky, *Cluster algebras II: Finite type
classification*, Invent. Math. 154 (2003), Theorem 1.8: a cluster algebra has finitely many
cluster variables exactly when every exchange matrix `B` in its mutation class satisfies
`|bᵢⱼ bⱼᵢ| ≤ 3`. The companion statement of Theorem 1.4, that these cluster algebras correspond
to the Cartan matrices of finite type (types `A_n, B_n, C_n, D_n, E_6, E_7, E_8, F_4, G_2`), is
not formalised here.
-/

@[expose] public section

namespace MathlibExt.RingTheory.ClusterAlgebra.FiniteTypeWanted

open MathlibExt.RingTheory.ClusterAlgebra
open MathlibExt.RingTheory.ClusterAlgebra.LaurentPhenomenonWanted

/-- **Finite type criterion for cluster algebras.** For a skew-symmetrizable integer matrix `B`,
the coefficient-free seed pattern through `((X_i), B)` has finitely many cluster variables if
and only if every matrix `B'` obtained from `B` by iterated mutation satisfies
`|b'ᵢⱼ b'ⱼᵢ| ≤ 3` for all `i, j` (Fomin and Zelevinsky, *Cluster algebras II: Finite type
classification*, Invent. Math. 154 (2003), Theorem 1.8, (ii) ⇔ (iii)). The source theorem is
for arbitrary coefficients and sign-skew-symmetric `B`; this is its coefficient-free,
skew-symmetrizable case. -/
theorem_wanted finite_clusterVariables_iff {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℤ) (hB : IsSkewSymmetrizable B) :
    (clusterVariables (initialCluster n, B)).Finite ↔
      ∀ (w : List n) (i j : n),
        |(mutateSeq w (initialCluster n, B)).2 i j * (mutateSeq w (initialCluster n, B)).2 j i| ≤ 3

end MathlibExt.RingTheory.ClusterAlgebra.FiniteTypeWanted
