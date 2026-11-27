# Proper-clause satisfiability probability

For $n,k\in\mathbb N$, a proper $k$-clause on $[n]$ is a function from the $n$ variables to optional Boolean signs with exactly $k$ nonempty entries. It is equivalent to a $k$-element variable set and a choice of Boolean sign on that set. An ordered formula of length $m$ is a list indexed by $[m]$ of such clauses, allowing repetitions. A clause is satisfied by an assignment if it agrees with one specified sign; the formula is satisfiable if one assignment satisfies every clause.

Write $p(n,k,m)$ for the real quotient of the number of satisfiable ordered formulas by the number of ordered formulas, with totalized division. This gives $p(n,k,0)=1$ even for $n<k$, and $p(n,k,m)=0$ for $m>0$ and $n<k$. When $n\ge k$ the counting law is the product of independent clause draws, each obtained by a uniform $k$-element subset followed by independent fair signs. For $k=3$ use the canonical 3-SAT probability: extend the signs by false on absent variables, as required by the canonical clause subtype; the resulting bijection of ordered formulas preserves satisfaction.

## Depends on

- [Satisfiability probability of random 3-SAT](../random-3-sat-threshold/sat-prob.md)

## Sources

- [Canonical 3-clause in Atlas](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/CSLibExt/Combinatorics/RandomThreeSat.lean#L51-L66)
- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/FixedClauseThreshold.lean#L20-L40)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SATComputability.lean#L7-L26)
