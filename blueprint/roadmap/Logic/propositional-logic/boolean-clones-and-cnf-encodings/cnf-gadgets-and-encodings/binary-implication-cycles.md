# Binary implication cycles and chains

For a list of variables $x_1,\dots,x_k$ ($k \ge 1$), the *implication cycle* is the 2-CNF formula $\bigwedge_{i=1}^{k} (\neg x_i \vee x_{i+1})$ with indices taken modulo $k$; each variable occurs exactly twice. An assignment satisfies it if and only if $x_1,\dots,x_k$ all receive the same truth value. An *implication chain* drops the closing clause $\neg x_k \vee x_1$; it forces $x_1 \to x_2 \to \dots \to x_k$, so a true last variable forces a true first one when the chain is oriented backwards.

## Depends on

- [2-CNF formulas](../../2-satisfiability/is-two-cnf.md)

## Sources

- C. H. Papadimitriou, Computational Complexity, Addison-Wesley, 1994.
