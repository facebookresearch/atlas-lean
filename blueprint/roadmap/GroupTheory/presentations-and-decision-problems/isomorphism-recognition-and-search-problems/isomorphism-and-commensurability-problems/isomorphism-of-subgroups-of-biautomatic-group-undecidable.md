# Isomorphism of finitely presented subgroups of some biautomatic CAT(0) group is undecidable

There is a compact non-positively curved cubical complex with biautomatic fundamental group $G$ and a recursive family of finitely presented subgroups $H_n \subseteq G$ such that no algorithm decides whether $H_n$ is isomorphic to $H_1$.

A finitely generated group is *biautomatic* if it admits a biautomatic structure in the sense of Epstein, Cannon, Holt, Levy, Paterson and Thurston; fundamental groups of compact non-positively curved cubical complexes and hyperbolic groups are examples.

**Theorem (Baumslag–Bridson–Miller–Short).** There exist a non-positively curved $4$-dimensional cubical complex $K$ with biautomatic fundamental group $G$ and a recursive class of finitely presented subgroups $H_n \subseteq G$ $(n \in \mathbb{N})$ such that there is no algorithm to determine whether or not $H_n$ is (abstractly) isomorphic to $H_1$.

Conventions: the subgroups are given by explicit finite presentations and explicit embeddings into $G$; the group $G$ is a direct product $\hat{\Gamma} \times \Gamma$ of a torsion-free word-hyperbolic group $\Gamma$ and an HNN extension $\hat{\Gamma}$ of $\Gamma$ along a maximal cyclic subgroup. As a consequence, there is a closed non-positively curved manifold $M$ of dimension $9$ and a recursive class of finitely presented subgroups of $\pi_1 M$ for which homotopy equivalence of the corresponding covering spaces is undecidable.

## Depends on

- [Word-hyperbolic groups](../../../geometric-group-theory/hyperbolic-groups/is-hyperbolic.md)
- [Automatic group](../../../free-groups/automorphisms-of-free-groups/automaticity-of-automorphism-groups-of-free-grou/is-automatic-group.md)
- [Group](../../../group-basics/group.md)

## Proof depends on

None.

## Expansion

Start from a group $Q$ of type $F_3$ with unsolvable word problem and apply the enhanced Rips construction to obtain $1 \to N \to \Gamma \to Q \to 1$ with $\Gamma$ torsion-free hyperbolic. For each word $w$ in the generators of $Q$ the authors build, inside $\hat{\Gamma}_1 \times \Gamma$, a finitely presented subgroup $\hat{P}_w$ extending the fiber product of the sequence, with explicit presentations obtained from the 1-2-3 Theorem; then $\hat{P}_w \cong \hat{P}_1$ exactly when $w = 1$ in $Q$. The case $w \ne 1$ is detected through the structure of centralizers of elements in HNN extensions. The groups of type $F_3$ with unsolvable word problem, the enhanced Rips construction and the 1-2-3 Theorem have no page here.

## Sources

- Gilbert Baumslag, Martin R. Bridson, Charles F. Miller III and Hamish Short, *Fibre products, non-positive curvature, and decision problems*, Comment. Math. Helv. 75 (2000), no. 3, 457–477, https://doi.org/10.1007/s000140050136, read in the open-access publisher copy at https://ems.press/content/serial-article-files/42872: the statement is Theorem B of its introduction, the consequence for manifolds is Corollary C, and the proof is Theorem 4.3 with Lemma 4.4.
