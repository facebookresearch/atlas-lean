# A finitely presented group with decidable power problem but undecidable power problem of order two

There is a finitely presented group with decidable conjugacy problem in which one can decide whether an element is a power of another, but cannot decide whether an element is a product $g_1^{z_1} g_2^{z_2}$ of powers of two given elements.

For a group $G$ given by a recursive presentation and $n \ge 1$, let $\mathrm{P}[n]$ be the set of tuples $(g_0, g_1, \dots, g_n) \in G^{n+1}$ for which the equation $g_0 = g_1^{z_1} \cdots g_n^{z_n}$ has a solution $(z_1, \dots, z_n) \in \mathbb{Z}^n$; the power problem of order $n$ is the membership problem for $\mathrm{P}[n]$, with elements given as words in the generators. The case $n = 1$ is the power problem.

There exists a finitely presented group $G$ such that $\mathrm{P}[1]$ is decidable and $\mathrm{P}[2]$ is undecidable; moreover $G$ has decidable conjugacy problem (Theorem A of the source).

The source allows recursive presentations on countably many generators, as for the auxiliary group of Proposition 2.1; the group $G$ of the theorem is finitely presented, so it is recursively presented in the finitely generated sense of the linked page. Decidability of $\mathrm{P}[n+1]$ implies decidability of $\mathrm{P}[n]$, by padding with the identity, so the theorem shows that this hierarchy is strict at its first step.

## Depends on

- [Power problem of a finitely generated group](../../conjugacy-order-and-power-problems/order-and-power-problems/power-problem.md)
- [Group](../../../group-basics/group.md)
- [Recursively presented group](../../../orderable-groups/word-problem-for-orderable-groups/is-recursively-presented.md)
- [Solvable conjugacy problem for a quotient of a free group](../../decision-problems-in-free-abelianized-extensions/conjugacy-problem-solvable.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Proposition 2.1 of the source constructs a recursively presented group $G_0$ with decidable $\mathrm{P}[1]$ and undecidable $\mathrm{P}[2]$. A computable embedding of $G_0$ into a finitely presented group with decidable conjugacy and power problems, built from embedding theorems of Olshanskii and Sapir, preserves the solution sets of the equations $g_0 = g_1^x g_2^y$ with coefficients in $G_0$, so $\mathrm{P}[2]$ stays undecidable.

## Sources

- O. Bogopolski and A. Ivanov, "Decidability problem for exponential equations in finitely presented groups", Canadian Mathematical Bulletin 66 (2023), no. 3, 731–748, https://doi.org/10.4153/s0008439522000698; read in arXiv:2105.06842v1 (titled "Notes about decidability of exponential equations") (Theorem A in the introduction, Proposition 2.1 and the proof of Theorem A in Section 3 of arXiv:2105.06842v1).
