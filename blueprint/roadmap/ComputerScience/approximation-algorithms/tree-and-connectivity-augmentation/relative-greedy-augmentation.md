# Relative greedy algorithms for weighted tree augmentation

Fix a WTAP instance, which may be assumed shadow-complete: for every link $\ell$ and distinct $v_1,v_2$ on $P_\ell$, the link $v_1v_2$ is present with weight $w(\ell)$. Let $U$ be an optimal up-link solution. For $C \subseteq L$ let $\mathrm{Drop}_U(C)=\{u \in U : P_u \subseteq \bigcup_{\ell \in C}P_\ell\}$ be the up-links made redundant by $C$. Given a family $\mathcal{K}$ of candidate link sets (components), a relative greedy algorithm repeats: choose $C \in \mathcal{K}$ minimizing

$$
\frac{w(C)}{w(\mathrm{Drop}_U(C))},
$$

add $C$ to the solution, delete $\mathrm{Drop}_U(C)$ from $U$ and contract the covered tree edges, until $U=\emptyset$. The output is the union of all chosen components together with no remaining up-links. This scheme originates in Zelikovsky's Steiner tree algorithm.

## Depends on

- [Weighted tree augmentation problem (WTAP)](weighted-tree-augmentation.md)
- [Frederickson-JaJa: weighted tree augmentation is 2-approximable by splitting links](frederickson-jaja-two-approx.md)

## Sources

- Alexander Z. Zelikovsky, "An 11/6-Approximation Algorithm for the Network Steiner Problem", Algorithmica (1993).
- Nachshon Cohen, Zeev Nutov, "A (1+ln 2)-Approximation Algorithm for Minimum-Cost 2-Edge-Connectivity Augmentation of Trees with Constant Radius", Theoretical Computer Science (2013).
- Vera Traub, Rico Zenklusen, "A Better-Than-2 Approximation for Weighted Tree Augmentation", FOCS (2021), arXiv:2104.07114.
