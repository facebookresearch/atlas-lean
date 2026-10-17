---
article_id: af_9025e0120cacaee555ed2bfd
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.cameron_symmetricGroup_closed_highlyHomogeneous
---

# Cameron Symmetric Group

Cameron representative `S`: the full symmetric group is closed and highly homogeneous.

Scope: this proves only the representative `S`, not Cameron's exhaustive classification,
uniqueness, conjugacy, Parker-sequence claims, or the other four representatives.

References:
- Daniele A. Gewurz and Francesca Merola, *Sequences realized as Parker vectors of
  oligomorphic permutation groups*, Journal of Integer Sequences 6, source lines 331--359 at
  https://cs.uwaterloo.ca/journals/JIS/VOL6/Gewurz/gewurz22.tex; source SHA-256
  `aa62fa83a5a0944c6903374ab69e7ab8d597622de49c86684e44b75f76baca21`, span SHA-256
  `81f32b07c6496d97cbe329c5facf9480104f4afa49b8dfc347b1fd6b1e4f93c4`.
- Peter J. Cameron, "Transitivity of permutation groups on unordered sets,"
  *Mathematische Zeitschrift* 148(2) (1976), 127--139, DOI 10.1007/BF01214702.

Representation choice: `S` is the full symmetric group on the countably infinite set `ℚ`,
written `(⊤ : Subgroup (Equiv.Perm ℚ))`, with `ℚ` serving as a canonical countably
infinite carrier. The topology on `Equiv.Perm ℚ` is `Equiv.Perm.pointwiseTopology`
(pointwise convergence); the ordinary topology on `ℚ` itself is untouched.

## Depends on

- [Pointwise Topology](pointwise-topology.md)
- [Is Highly Homogeneous](highly-homogeneous/is-highly-homogeneous.md)

## Proof depends on

- [Is Highly Homogeneous top](highly-homogeneous/is-highly-homogeneous-top.md)

## Sources

- [MathlibExt, MathlibExt.GroupTheory.Permutation.CameronSymmetricGroup](../../../../../sources/v2/MathlibExt.md)
