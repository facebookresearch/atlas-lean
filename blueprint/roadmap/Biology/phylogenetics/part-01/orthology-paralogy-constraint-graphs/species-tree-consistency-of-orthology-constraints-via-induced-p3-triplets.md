# Species-tree consistency of orthology constraints via induced P3 triplets

**Setting.** Use the DS-trees and constraint graphs $R = (V, E, U)$ of
[satisfiability of partial orthology and paralogy constraints](satisfiability-of-partial-orthology-and-paralogy-constraints.md).
A **species tree** $S$ is a rooted tree on the species set $\Sigma$. A DS-tree $G$ is **consistent** with
$S$ if, for every speciation node $x$ of $G$ and children $y, z$ of $x$, the nodes
$\mathrm{lca}_S(s(L_y))$ and $\mathrm{lca}_S(s(L_z))$ are unrelated in $S$ (neither is an ancestor of the
other). Its **speciation triplets** are

$$\mathrm{tr}_S(G) = \{\, s(x)s(y) \mid s(z) : xy \mid z \text{ is a rooted triplet of } G \text{ rooted at a speciation},\ s(x) \ne s(y) \,\},$$

and $G$ is consistent with $S$ if and only if $S$ displays every triplet of $\mathrm{tr}_S(G)$. $R$ is
**consistent with** $S$ if some realization of $R$ is satisfied by a DS-tree consistent with $S$, and
**consistent** if it is consistent with some species tree.

**Theorem (given species tree).** If $|V| = 1$, $R$ is consistent with every $S$ (its DS-tree is a single leaf). If $|V| \ge 2$, $R$ is consistent with $S$ if and only if

1. $R(\emptyset)$ is disconnected and each connected component is consistent with $S$; or
2. $\overline{R(U)}$ is disconnected, its components admit a **speciation partition** (a partition into
   at least two parts $P_i$ with $\mathrm{lca}_S(s(P_i))$ pairwise unrelated), and each part is
   consistent with $S$.

This yields an $O(n^3)$ algorithm when $|\mathcal{G}| \ge |\Sigma|$.

**Theorem (unknown species tree, full constraints).** Let $R = (V, E, \emptyset)$ be a satisfiable full
constraint graph and

$$P_3(R) = \{\, s(x)s(y) \mid s(z) : zx, zy \in E,\ xy \notin E,\ s(x) \ne s(y) \,\},$$

the species triplets read off induced paths $x - z - y$. Then $R$ is consistent if and only if some
species tree displays all triplets of $P_3(R)$. Hence consistency is decidable in polynomial time by
running the BUILD algorithm on $P_3(R)$, without first constructing a DS-tree.

**Trivial cases.** Any set of orthology constraints alone, and any set of paralogy constraints alone,
is consistent (with the star species tree).

## Depends on

- [Satisfiability of partial orthology and paralogy constraints](satisfiability-of-partial-orthology-and-paralogy-constraints.md)
- [Rooted triplet](../../splits-compatibility-ultrametrics-and-upgma/triplet.md)
- [Cluster system displaying a triplet](../../splits-compatibility-ultrametrics-and-upgma/displays-triplet.md)

## Proof depends on

- [Correctness of BUILD](../../splits-compatibility-ultrametrics-and-upgma/build-spec.md)

## Expansion

An induced path $x - z - y$ forces $\mathrm{lca}_G(x, y)$ to be a duplication strictly below the
speciation $\mathrm{lca}_G(x, z) = \mathrm{lca}_G(y, z)$, so every satisfying DS-tree carries the
speciation triplet $s(x)s(y) \mid s(z)$: $P_3(R)$ is necessary. For sufficiency, contract adjacent
speciation nodes to get a least-resolved satisfying tree. A speciation triplet $xy \mid z$ of that tree
is either itself an induced $P_3$ or has a duplication between $\mathrm{lca}(x, y)$ and the root of the
triplet, which supplies a leaf $d$ with $\{x, d, z\}$ and $\{y, d, z\}$ both induced $P_3$s; any species
tree displaying those two triplets displays $s(x)s(y) \mid s(z)$. With unknown edges the paper gives an
exact branch-and-bound algorithm that is exponential in the worst case.

## Sources

- M. Lafond, N. El-Mabrouk, "Orthology and paralogy constraints: satisfiability and consistency",
  BMC Genomics 15(Suppl 6) (2014) S12, Definitions 1 and 4, Theorem 1, Lemma 4, Theorems 4-5 and
  algorithms FindSpeciationPartition and CheckCons, <https://doi.org/10.1186/1471-2164-15-s6-s12>
  (PMC4240720).
