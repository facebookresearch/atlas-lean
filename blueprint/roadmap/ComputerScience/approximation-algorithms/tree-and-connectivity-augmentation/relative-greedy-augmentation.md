# Relative greedy algorithms for weighted tree augmentation

Fix a WTAP instance, which may be assumed shadow-complete: for every link $\ell$ and distinct $v_1,v_2$ on $P_\ell$, a link $v_1v_2$ (a shadow of $\ell$) of weight $w(\ell)$ is present. Shadows are added as separate copies labelled by their origin $\ell$, so shadows of different links with the same endpoints are parallel links that may have different weights (keeping only the cheapest copy, with its origin, is equivalent); a selected shadow is finally replaced by its origin without changing the weight. Root the tree at a vertex $r$; an up-link is a link one of whose endpoints lies on the tree path from $r$ to the other endpoint. For a set $U$ of up-links and $C \subseteq L$ let

$$
\mathrm{Drop}_U(C)=\Big\{u \in U : P_u \subseteq \bigcup_{\ell \in C}P_\ell\Big\}
$$

be the up-links made redundant by $C$. For an integer $k \ge 0$, a link set $C$ is $k$-thin if every vertex lies on the paths $P_\ell$ of at most $k$ links $\ell \in C$. For fixed $\varepsilon > 0$, the relative greedy algorithm of Traub and Zenklusen (Algorithm 1) proceeds as follows.

For a current up-link set $U$, the ratio of a candidate $C$ is

$$
\frac{w(C)}{w(\mathrm{Drop}_U(C))},
$$

interpreted as $+\infty$ when $\mathrm{Drop}_U(C)=\emptyset$. The algorithm first computes a WTAP solution $U$ consisting of up-links whose paths $P_u$, $u \in U$, are pairwise edge-disjoint, with $w(U) \le 2\,\mathrm{OPT}$, and sets $F=\emptyset$. While $U \ne \emptyset$, it chooses a $\lceil 2/\varepsilon \rceil$-thin link set $C \subseteq L$ of minimum ratio, adds $C$ to $F$ and replaces $U$ by $U \setminus \mathrm{Drop}_U(C)$. Finally it returns $F$.

The tree is never contracted: the test $\mathrm{Drop}_U(C)$ always refers to the original paths $P_u$ and $P_\ell$, only the set $U$ shrinks. Every single up-link $u \in U$ is itself a $1$-thin candidate with $\mathrm{Drop}_U(\{u\}) \ni u$, so each chosen ratio is at most $1$ and the loop terminates; $U \cup F$ remains a WTAP solution throughout. This scheme originates in Zelikovsky's Steiner tree algorithm; Cohen and Nutov used it with constant-size components for WTAP on trees of bounded radius.

## Depends on

- [Weighted tree augmentation problem (WTAP)](weighted-tree-augmentation.md)

## Sources

- Alexander Z. Zelikovsky, "An 11/6-Approximation Algorithm for the Network Steiner Problem", Algorithmica (1993).
- Nachshon Cohen, Zeev Nutov, "A (1+ln 2)-Approximation Algorithm for Minimum-Cost 2-Edge-Connectivity Augmentation of Trees with Constant Radius", Theoretical Computer Science (2013).
- Vera Traub, Rico Zenklusen, "A Better-Than-2 Approximation for Weighted Tree Augmentation", FOCS (2021), arXiv:2104.07114, Section 3 (Lemmas 2 and 4, Definition 3, Algorithm 1).
