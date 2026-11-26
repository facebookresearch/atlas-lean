# Pigeonhole formulas $\mathrm{PHP}^m_n$

For $m, n \ge 0$ the pigeonhole formula $\mathrm{PHP}^m_n$ has a variable $p_{i,j}$ for each pigeon $i \in [m]$ and hole $j \in [n]$ (read "pigeon $i$ sits in hole $j$"), the *pigeon clauses* $\bigvee_{j \in [n]} p_{i,j}$ for every $i$, and the *hole clauses* $\neg p_{i,j} \vee \neg p_{i',j}$ for every hole $j$ and pigeons $i \ne i'$. It is satisfiable if and only if $m \le n$. It has $mn$ variables and $m + n\binom{m}{2}$ clauses; for $m > n$ it is the classical unsatisfiable family, the *weak* pigeonhole principle when $m \gg n$.

## Depends on

- [CNF formula](../../propositional-logic/conjunctive-normal-form/cnf.md)

## Sources

- A. Haken, "The Intractability of Resolution", Theoretical Computer Science 39, 297–308, 1985.
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021.
