# Cutting planes polynomially simulate resolution

Every resolution refutation of a CNF formula with $s$ lines translates line by line into a cutting planes refutation of its inequality translation with $O(s \cdot N)$ lines, where $N$ is the number of variables. A resolution step from $A \vee v$ and $B \vee \neg v$ to $A \vee B$ is simulated by adding the two inequalities, which cancels $v$, adding the axioms $\ell \ge 0$ for the literals occurring in only one of $A$, $B$ so that every coefficient becomes $2$, and dividing by $2$ with rounding.

## Proof sketch

After addition the inequality reads $\sum_{\ell \in A} \ell + \sum_{\ell \in B} \ell \ge 1$ with coefficient $2$ on shared literals; adding $\ell \ge 0$ for literals in only one of $A, B$ makes all coefficients $2$, and rounded division by $2$ gives $\sum_{\ell \in A\cup B} \ell \ge \lceil 1/2 \rceil = 1$.

## Depends on

- [The cutting planes proof system](cutting-planes-proof-system.md)
- [Resolution refutation](../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Sources

- W. Cook, C. R. Coullard and Gy. Turán, "On the Complexity of Cutting-Plane Proofs", Discrete Applied Mathematics 18(1), 25–38, 1987.
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021, Sections 7.6.1 and 7.7.2.
- S. Jukna, Boolean Function Complexity: Advances and Frontiers, Springer, 2012.
