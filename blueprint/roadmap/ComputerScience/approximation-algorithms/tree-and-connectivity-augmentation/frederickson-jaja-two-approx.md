# Frederickson-JaJa: weighted tree augmentation is 2-approximable by splitting links

Root the tree $G$ of a WTAP instance at a vertex $r$. Replace every link $\ell=uv$ by the two up-links $u\,\mathrm{lca}(u,v)$ and $v\,\mathrm{lca}(u,v)$, each of weight $w(\ell)$, where $\mathrm{lca}$ is the lowest common ancestor. A minimum-weight set of up-links covering $E$ can be computed in polynomial time (the up-link covering matrix is totally unimodular, and the problem is a shortest arborescence problem), and mapping each chosen up-link back to a link yields a WTAP solution of weight at most $2\,\mathrm{OPT}$. The natural cut LP of WTAP has integrality gap at most $2$.

## Proof sketch

Every link of an optimal solution yields two up-links covering exactly the same tree edges, so the up-link optimum is at most $2\,\mathrm{OPT}$, and in fact at most twice the cut LP value. For up-links the constraint matrix has the consecutive-ones property along root paths, hence is totally unimodular, so the up-link LP has an integral optimum. Mapping up-links back to their original links never increases the weight and keeps coverage.

## Depends on

- [Weighted tree augmentation problem (WTAP)](weighted-tree-augmentation.md)
- [Approximation algorithms and approximation ratios](../approximation-algorithms-and-approximation-ratios.md)
- [Classical approximation guarantees](../lp-based-approximation/classical-approximation-guarantees.md)
- [Integrality gaps of linear programming relaxations](../lp-based-approximation/integrality-gaps-of-linear-programming.md)

## Proof depends on

- [Weighted tree augmentation problem (WTAP)](weighted-tree-augmentation.md)
- [Integrality gaps of linear programming relaxations](../lp-based-approximation/integrality-gaps-of-linear-programming.md)

## Sources

- Greg N. Frederickson, Joseph JaJa, "Approximation Algorithms for Several Graph Augmentation Problems", SIAM Journal on Computing (1981).
- Samir Khuller, Ramakrishna Thurimella, "Approximation Algorithms for Graph Augmentation", Journal of Algorithms (1993).
