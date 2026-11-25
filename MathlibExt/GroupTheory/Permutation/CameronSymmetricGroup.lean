/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.Permutation.HighlyHomogeneous
public import MathlibExt.GroupTheory.Permutation.PointwiseTopology

namespace MetaMathlibExt

@[expose] public section

/-- **The symmetric group of the rationals is closed and highly homogeneous.** Let
$\operatorname{Sym}(\mathbb{Q})$ be the group of all permutations of the set $\mathbb{Q}$. Then
$\operatorname{Sym}(\mathbb{Q})$ is closed in the topology of pointwise convergence on the
permutations of $\mathbb{Q}$, and it is highly homogeneous: for every natural number $k$ it has a
single orbit on the $k$-element subsets of $\mathbb{Q}$.

Here $\mathbb{Q}$ serves only as a countably infinite set; its order, its field structure and its
usual topology play no role.

Source: Daniele A. Gewurz and Francesca Merola, *Sequences realized as Parker vectors of
oligomorphic permutation groups*, Journal of Integer Sequences 6, source lines 331--359 at
https://cs.uwaterloo.ca/journals/JIS/VOL6/Gewurz/gewurz22.tex; source SHA-256
`aa62fa83a5a0944c6903374ab69e7ab8d597622de49c86684e44b75f76baca21`, span SHA-256
`81f32b07c6496d97cbe329c5facf9480104f4afa49b8dfc347b1fd6b1e4f93c4`. Peter J. Cameron,
"Transitivity of permutation groups on unordered sets," *Mathematische Zeitschrift* 148(2)
(1976), 127--139, DOI 10.1007/BF01214702. Scope: this proves only Cameron's representative S,
not Cameron's exhaustive classification, uniqueness, conjugacy, Parker-sequence claims, or the
other four representatives. -/
public theorem cameron_symmetricGroup_closed_highlyHomogeneous :
    @IsClosed (Equiv.Perm ℚ) (Equiv.Perm.pointwiseTopology (α := ℚ))
        (↑(⊤ : Subgroup (Equiv.Perm ℚ)) : Set (Equiv.Perm ℚ)) ∧
      IsHighlyHomogeneous (⊤ : Subgroup (Equiv.Perm ℚ)) := by
  constructor
  · rw [Subgroup.coe_top]
    exact @isClosed_univ _ (Equiv.Perm.pointwiseTopology (α := ℚ))
  · exact isHighlyHomogeneous_top

end

end MetaMathlibExt
