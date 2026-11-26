# Tree-like resolution of the pigeonhole principle needs $2^{\Omega(n \log n)}$ size

For all $m > n$ and $0 \le h \le n$, every tree-like resolution refutation of $\mathrm{PHP}^m_n$ has at least $(n + 1 - h)^h$ nodes. Taking $h = \lfloor n/2 \rfloor$ gives at least $(n/2 + 1)^{n/2} = 2^{\Omega(n \log n)}$ nodes, independently of the number $m$ of pigeons. This is the Beyersdorff–Galesi–Lauria bound, matching the Dantchev–Riis bound for the weak pigeonhole principle up to constants in the exponent.

## Proof sketch

Define the potential of a partial matching-like assignment as a product over pigeons of the number of holes still available, so that each query splits the potential subadditively; apply the Prover–Delayer potential lemma and evaluate the potential at the empty assignment with the first $h$ pigeons.

## Depends on

- [Pigeonhole formulas $\mathrm{PHP}^m_n$](../resolution-lower-bounds/pigeonhole-formulas.md)
- [Tree-like resolution derivation](../../propositional-logic/resolution-size-and-width/resolution-tree.md)

## Proof depends on

- [Prover–Delayer potentials bound tree-like refutation size](prover-delayer-potentials.md)

## Sources

- O. Beyersdorff, N. Galesi and M. Lauria, "A Lower Bound for the Pigeonhole Principle in Tree-Like Resolution by Asymmetric Prover–Delayer Games", Information Processing Letters 110(23), 1074–1077, 2010.
- S. Dantchev and S. Riis, "Tree Resolution Proofs of the Weak Pigeon-Hole Principle", Proceedings of the 16th IEEE Conference on Computational Complexity, 2001.
