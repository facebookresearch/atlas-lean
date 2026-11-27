# Tree-like resolution of the pigeonhole principle needs $2^{\Omega(n \log n)}$ size

For all $m > n$ with $n$ even, every tree-like resolution refutation of $\mathrm{PHP}^m_n$ has size at least $2^{(n/2)\log_2(n/2 + 1)} = (n/2 + 1)^{n/2} = 2^{\Omega(n \log n)}$, independently of the number $m$ of pigeons; the same bound holds for the functional pigeonhole principle. This is the Beyersdorff–Galesi–Lauria bound, matching the Dantchev–Riis bound for the weak pigeonhole principle up to constants in the exponent.

## Proof sketch

Let $p_i(\alpha)$ be the number of free holes already excluded for pigeon $i$, and score $c_0 = (n/2 + 1 - p_i)/(n/2 - p_i)$, $c_1 = n/2 + 1 - p_i$ for a query $x_{i,j}$. Delayer answers $0$ when pigeon $i$ already sits in a hole or hole $j$ is taken, puts pigeon $i$ into hole $j$ once $p_i \ge n/2$, and defers otherwise. The game then ends on a pigeon clause, at least $n/2$ pigeons have been placed, and each placed pigeon earns $\log_2(n/2 + 1)$ points; the asymmetric game theorem gives the bound.

## Depends on

- [Pigeonhole formulas $\mathrm{PHP}^m_n$](../resolution-lower-bounds/pigeonhole-formulas.md)
- [Tree-like resolution derivation](../../propositional-logic/resolution-size-and-width/resolution-tree.md)

## Proof depends on

- [Prover–Delayer potentials bound tree-like refutation size](prover-delayer-potentials.md)

## Sources

- O. Beyersdorff, N. Galesi and M. Lauria, "A Lower Bound for the Pigeonhole Principle in Tree-Like Resolution by Asymmetric Prover–Delayer Games", Information Processing Letters 110(23), 1074–1077, 2010: Section 4, Theorem 2 and its proof.
- S. Dantchev and S. Riis, "Tree Resolution Proofs of the Weak Pigeon-Hole Principle", Proceedings of the 16th IEEE Conference on Computational Complexity, 2001.
