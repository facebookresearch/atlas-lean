# Cutting planes polynomially simulate resolution

Cutting planes simulates resolution efficiently with respect to length and size by mimicking the resolution steps one by one: every resolution refutation of a CNF formula translates, step by step, into a cutting planes refutation of its inequality translation whose number of lines is polynomially bounded in the number of lines of the resolution refutation and the number of variables.

## Proof sketch

A resolution step from $A \vee v$ and $B \vee \neg v$ to $A \vee B$ is simulated by adding the two inequalities, which cancels $v$ and leaves $\sum_{\ell \in A} \ell + \sum_{\ell \in B} \ell \ge 1$ with coefficient $2$ on shared literals; adding the axioms $\ell \ge 0$ for the literals occurring in only one of $A$, $B$ makes every coefficient $2$, and rounded division by $2$ gives $\sum_{\ell \in A\cup B} \ell \ge \lceil 1/2 \rceil = 1$. (Derived, not stated by the sources: each step uses at most $N + 2$ cutting planes lines, where $N$ is the number of variables, so a resolution refutation with $s$ lines becomes a cutting planes refutation with $O(s \cdot N)$ lines.)

## Depends on

- [The cutting planes proof system](cutting-planes-proof-system.md)
- [Resolution refutation](../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Sources

- W. Cook, C. R. Coullard and Gy. Turán, "On the Complexity of Cutting-Plane Proofs", Discrete Applied Mathematics 18(1), 25–38, 1987.
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021, Section 7.7.2 (cutting planes simulates resolution with respect to length and size by mimicking the resolution steps one by one).
- S. Jukna, Boolean Function Complexity: Advances and Frontiers, Springer, 2012.
