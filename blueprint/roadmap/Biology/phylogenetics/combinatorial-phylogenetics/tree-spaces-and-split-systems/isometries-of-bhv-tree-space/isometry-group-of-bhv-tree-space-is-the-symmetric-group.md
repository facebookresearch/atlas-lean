# The isometry group of BHV tree space is the symmetric group

Let $n \ge 3$ and let $\mathrm{BHV}_n$ be the Billera–Holmes–Vogtmann space of unrooted phylogenetic trees with leaves labeled $1,\dots,n$, parametrized by internal edge lengths. It is made of $(2n-5)!!$ orthants $\mathbb{R}_{\ge 0}^{n-3}$, one per binary topology. Two orthants are glued along the faces where the edges they do not share have length $0$. The space carries the path metric that is Euclidean on each orthant. Equivalently, $\mathrm{BHV}_n$ is the right-angled spherical metric cone over the flag simplicial complex $L_n$, whose vertices are the nontrivial splits of $[n]$ and whose simplices are the sets of pairwise compatible splits.

**Theorem.** Let $n\ge5$. The action of $S_n$ on $\mathrm{BHV}_n$ by permuting leaf labels is faithful, and it is the whole isometry group: $\mathrm{Isom}(\mathrm{BHV}_n)\cong S_n$, and every isometry is induced by a unique permutation of the leaf labels.

The two smaller cases are exceptions. For $n=3$ there is a single orthant $\mathbb R_{\ge0}^0$, so $\mathrm{BHV}_3$ is a point and its isometry group is trivial. For $n=4$ there are three orthants $\mathbb R_{\ge0}$, one for each split $\{12|34\},\{13|24\},\{14|23\}$, glued at their origins, so $\mathrm{BHV}_4$ is a tripod of three rays and its isometry group is $S_3$; leaf permutations induce all of these isometries through the surjection $S_4\to S_3$ on the three splits, whose kernel is the Klein four-group, so the action is not faithful.

In the more common convention, where trees have leaves labeled $0,1,\dots,n$ and tree space has orthants of dimension $n-2$, the statement reads: for $n\ge4$ the isometry group is $S_{n+1}$, acting faithfully by relabeling; for $n=2$ it is trivial and for $n=3$ it is $S_3$.

## Depends on

- [Tree space](../../../../not-yet-classified/phylogenetic-tree-space/tree-space.md)
- [BHV distance](../../../../not-yet-classified/phylogenetic-tree-space/bhv-dist.md)

## Expansion

Permuting leaf labels clearly gives isometries, and for $n\ge5$ a nontrivial permutation moves some split, so the action is faithful; the content is the converse. The proof has three stages, each for $n\ge5$.

1. *Combinatorics of the link.* In the 1-skeleton $L_n^1$, the vertex for a split whose smaller side has $k$ elements has degree $2^k + 2^{n-k} - n - 4$ (Lemma 2.2). Splits with the same smaller-side size are compatible exactly when the smaller sides are disjoint (Lemma 2.3), so $L_n^1$ contains a Kneser graph $KG_{n,k}$ for each such $k$. The Erdős–Ko–Rado theorem then shows $\mathrm{Aut}(L_n^1) \cong S_n$ (Proposition 2.5). For $n=4$ the link $L_4$ is three isolated vertices, with automorphism group $S_3$, which is where the small cases separate. Since $L_n$ is flag, it has the same simplicial automorphisms (Corollary 2.6).
2. *Volume rigidity.* Isometries preserve the orthant-wise Lebesgue measure $\mu$ (Lemma 2.7). For a point $x$ with $p$ positive internal edges and $\epsilon$ below its smallest such edge, $A_{n-3}(\epsilon) \le \mu(B_x(\epsilon)) \le (2n-2p-5)!!\, 2^{p-(n-3)} A_{n-3}(\epsilon)$, where $A_m(\epsilon)$ is the volume of a Euclidean $m$-ball (Lemma 2.8). For $n \ge 4$, the cone point (the star tree) is therefore the unique point with maximal small-ball volume (Corollary 2.9), so every isometry fixes it.
3. *Reduction to the link.* An isometry fixing the cone point preserves the unit sphere $L_n$, and an isometry of the right-angled spherical complex $L_n$ is a simplicial automorphism. Stage 1 then identifies it with a leaf relabeling.

The result is used in statistical tests on tree space whose null distributions are built from label symmetries: the only symmetries available are relabelings of the leaves.

## Sources

- G. Grindstaff, "The isometry group of phylogenetic tree space is $S_n$", Proceedings of the American Mathematical Society 148 (2020) 4225–4233, <https://doi.org/10.1090/proc/15154>; preprint arXiv:1901.02982. Theorem 2.1 (main theorem; it is printed for a range of $n$ that includes the exceptional cases $n=3,4$, which the statement above excludes), Lemmas 2.2, 2.3, 2.7, 2.8, Proposition 2.5, Corollaries 2.6 and 2.9.
