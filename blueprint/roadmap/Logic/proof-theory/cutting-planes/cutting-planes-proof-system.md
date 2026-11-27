# The cutting planes proof system

Lines of cutting planes are integer linear inequalities $\sum_v a_v x_v \ge b$ ($a_v, b \in \mathbb{Z}$, finitely many nonzero $a_v$) over variables ranging over $\{0,1\}$. The axioms are $x_v \ge 0$ and $-x_v \ge -1$ and the inequalities of the input system. The rules are *addition* of two lines, *multiplication* of a line by a positive integer, and *Chvátal–Gomory rounded division*: from $\sum_v c\,a_v x_v \ge b$ with $c > 0$ infer $\sum_v a_v x_v \ge \lceil b/c \rceil$. A *refutation* derives $0 \ge 1$; its *size* is its number of lines. A clause $\ell_1 \vee \dots \vee \ell_k$ is translated as $\sum_i \ell_i \ge 1$ with $\neg x$ read as $1 - x$.

## Depends on

- [Cook–Reckhow propositional proof systems](../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)
- [Farkas certificates for linear rational arithmetic](../../../TheoryOfComputation/decision-procedures/satisfiability-modulo-theories/farkas-certificates-for-linear-rational.md)

## Sources

- W. Cook, C. R. Coullard and Gy. Turán, "On the Complexity of Cutting-Plane Proofs", Discrete Applied Mathematics 18(1), 25–38, 1987.
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021, Section 7.6.1 (rules (7.27a)–(7.27d)).
- V. Chvátal, "Edmonds Polytopes and a Hierarchy of Combinatorial Problems", Discrete Mathematics 4(4), 305–337, 1973.
