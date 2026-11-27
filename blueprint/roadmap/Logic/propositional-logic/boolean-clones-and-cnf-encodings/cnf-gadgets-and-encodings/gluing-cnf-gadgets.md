# Gluing CNF gadgets with private auxiliary variables

Let $\varphi_1,\dots,\varphi_m$ be CNF formulas over shared variables $V$ and auxiliary variables $W$, and form $\Phi = \bigwedge_i \varphi_i'$ where $\varphi_i'$ renames each auxiliary variable $w$ of $\varphi_i$ to a fresh copy $(i,w)$. Then an assignment $\sigma$ of $V$ extends to a model of $\Phi$ if and only if, for every $i$, $\sigma$ extends to a model of $\varphi_i$. This is the substitution rule behind gadget reductions to satisfiability.

## Proof sketch

The auxiliary variables of different sites are disjoint, so extensions can be chosen independently per site and glued.

## Depends on

- [CNF formula](../../conjunctive-normal-form/cnf.md)

## Sources

- M. R. Garey and D. S. Johnson, Computers and Intractability: A Guide to the Theory of NP-Completeness, W. H. Freeman, 1979.
- D. Lichtenstein, "Planar Formulae and Their Uses", SIAM Journal on Computing 11(2), 329–343, 1982.
