# Traub-Zenklusen local search: weighted tree augmentation is (1.5 + eps)-approximable

For every fixed $\varepsilon > 0$ there is a polynomial-time $(1.5+\varepsilon)$-approximation algorithm for WTAP, obtained by a non-oblivious local search over the components of the relative greedy framework. The same technique gives a purely combinatorial $(\ln 4+\varepsilon)$-approximation for the Steiner tree problem in graphs, with cost bounded by $(\ln 4+\varepsilon)$ times the value of the hypergraphic LP, and hence an alternative proof that the hypergraphic LP has integrality gap at most $\ln 4$.

## Proof sketch

The algorithm maintains a WTAP solution $F$ and, for every link $\ell=ab \in F$, a nonempty witness set $W_\ell$ of at most two up-link shadows of $\ell$, initially $\{a\,\mathrm{apex}(\ell),\ b\,\mathrm{apex}(\ell)\}$; the disjoint union $U$ of the witness sets is a WTAP solution, and shortening keeps the paths $P_u$, $u \in U$, pairwise edge-disjoint. Progress is measured by the potential

$$
\Phi(F)=\sum_{\ell \in F}H_{|W_\ell|}\,w(\ell)=\sum_{\ell \in F:\,|W_\ell|=1}w(\ell)+\sum_{\ell \in F:\,|W_\ell|=2}\tfrac32\,w(\ell),
$$

which weights each original link by the harmonic number of the number of its surviving witnesses. The weight of each link is spread over its witnesses: an up-link $u \in W_\ell$ gets $\bar w(u) = w(\ell)/|W_\ell|$, so that $\bar w(U) = w(F)$. A step computes a $\lceil 4/\varepsilon\rceil$-thin link set $C$ maximizing $\bar w(\mathrm{Drop}_U(C))-1.5\,w(C)$, removes $\mathrm{Drop}_U(C)$ from all witness sets, adds $C$ with fresh witness sets, shortens up-links, and deletes links whose witness sets became empty; it is repeated while $\Phi$ decreases by a factor of at least $1-\varepsilon/(6|V|)$. The potential decreases by at least $\bar w(\mathrm{Drop}_U(C))$ when the dropped witnesses are removed (removing one witness of $\ell$ lowers $H_{|W_\ell|}\,w(\ell)$ by $w(\ell)/|W_\ell|$, only half of $w(\ell)$ when $\ell$ has two witnesses) and increases by at most $1.5\,w(C)$ when $C$ is added; applying the decomposition theorem to an optimum and to $U$ with weights $\bar w$ shows that, at termination, the solution weight satisfies $w(F) \le (1.5+\varepsilon)\,\mathrm{OPT}$, the guarantee being on $w(F)$, not on $\Phi(F)$. For Steiner tree, full components play the role of link sets and the potential is compared against the hypergraphic LP.

## Depends on

- [Weighted tree augmentation problem (WTAP)](weighted-tree-augmentation.md)
- [Relative greedy algorithms for weighted tree augmentation](relative-greedy-augmentation.md)
- [Steiner tree instances](../../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/steiner-tree/steiner-tree-instance.md)
- [Integrality gaps of linear programming relaxations](../../lp-based-approximation/integrality-gaps-of-linear-programming.md)
- [Approximation algorithms and approximation ratios](../../approximation-algorithms-and-approximation-ratios.md)

## Proof depends on

- [Approximate decomposition of WTAP solutions into thin components (Traub-Zenklusen)](wtap-component-decomposition.md)
- [Traub-Zenklusen: weighted tree augmentation is (1 + ln 2 + eps)-approximable](tz-one-plus-ln-two.md)

## Sources

- Vera Traub, Rico Zenklusen, "Local Search for Weighted Tree Augmentation and Steiner Tree", SODA (2022), arXiv:2107.07403, Theorem 1.1, Sections 2.3–2.5 (Algorithm 1).
- Jaroslaw Byrka, Fabrizio Grandoni, Thomas Rothvoss, Laura Sanita, "Steiner Tree Approximation via Iterative Randomized Rounding", Journal of the ACM (2013).
