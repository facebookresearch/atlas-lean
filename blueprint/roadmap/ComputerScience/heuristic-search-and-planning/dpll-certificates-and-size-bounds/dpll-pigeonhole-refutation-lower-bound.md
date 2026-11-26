# DPLL refutations of pigeonhole formulas are exponential

Let $\mathrm{PHP}^{n+1}_n$ be the CNF formula stating that $n+1$ pigeons are mapped injectively into $n$ holes (variables $p_{ij}$, clauses $\bigvee_j p_{ij}$ for every pigeon $i$, and $\neg p_{ij} \vee \neg p_{i'j}$ for $i \ne i'$). For every numbering of its variables, the search tree of the DPLL solver on $\mathrm{PHP}^{n+1}_n$ has at least $2^{\lfloor n/2 \rfloor}$ leaves; hence both the tree-like resolution refutation and the LRAT certificate returned have at least $2^{\lfloor n/2 \rfloor}$ lines.

## Proof sketch

The failing search tree is a decision tree that finds a falsified clause on every assignment. The asymmetric Prover-Delayer game of Beyersdorff, Galesi and Lauria shows that every tree-like refutation of $\mathrm{PHP}^{n+1}_n$ has size at least $2^{n/2}$ in this sense: the Delayer can always keep $n/2$ pigeons free while scoring one point per Prover choice.

## Depends on

- [A DPLL solver that emits LRAT certificates](dpll-solver-with-lrat-certificates.md)
- [Tree-like resolution derivation](../../../Logic/propositional-logic/resolution-size-and-width/resolution-tree.md)

## Proof depends on

- [Failing DPLL search trees give tree-like resolution refutations](../../../Logic/propositional-logic/sat-solving/failing-dpll-search-trees-give-tree-like.md)

## Sources

- O. Beyersdorff, N. Galesi and M. Lauria, "A Lower Bound for the Pigeonhole Principle in Tree-like Resolution by Asymmetric Prover-Delayer Games", Information Processing Letters 110(23), 2010.
- M. Davis, G. Logemann and D. Loveland, "A Machine Program for Theorem-Proving", Communications of the ACM 5(7), 1962.
