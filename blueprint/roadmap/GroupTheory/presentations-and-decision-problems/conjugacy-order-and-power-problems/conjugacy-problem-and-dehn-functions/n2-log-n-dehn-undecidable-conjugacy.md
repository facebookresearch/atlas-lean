# Multiple HNN extensions of free groups with Dehn function n² log n and undecidable conjugacy problem

There are finitely presented multiple HNN extensions of free groups with Dehn function $n^2 \log n$ and undecidable conjugacy problem; $n^2 \log n$ is the smallest Dehn function of a multiple HNN extension of a free group with undecidable conjugacy problem.

A multiple HNN extension of a free group $F$ is a group $\langle F, t_1, \dots, t_k \mid t_i^{-1} u t_i = \phi_i(u)\ (u \in U_i,\ 1 \le i \le k) \rangle$ for finitely generated subgroups $U_i, V_i$ of $F$ and isomorphisms $\phi_i\colon U_i \to V_i$. Then (Theorem 1.1 of the source):

1. there exist finitely presented multiple HNN extensions of free groups with Dehn function $n^2 \log n$, and some of them have undecidable conjugacy problem;
2. conversely, if $d(n)$ is the Dehn function of a multiple HNN extension of a free group and the constructive limit of $d(n) / (n^2 \log n)$ as $n \to \infty$ is $0$, then the group has decidable conjugacy problem.

These were the first groups with Dehn function $n^2 \log n$.

## Depends on

- [Group](../../../group-basics/group.md)
- [Solvable conjugacy problem for a quotient of a free group](../../decision-problems-in-free-abelianized-extensions/conjugacy-problem-solvable.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The upper bound on Dehn functions comes from a new invariant of bipartite chord diagrams, used to estimate areas of van Kampen diagrams over multiple HNN extensions of free groups. The groups are built from $S$-machines; when the language of accepted words is not recursive, the set of conjugates of a fixed stop word is not recursive (Lemma 3.15 of the version read), so the conjugacy problem is undecidable.

## Sources

- A. Yu. Olshanskii and M. V. Sapir, "Groups with small Dehn functions and bipartite chord diagrams", Geometric and Functional Analysis 16 (2006), no. 6, 1324–1376, https://doi.org/10.1007/s00039-006-0580-9; read in arXiv:math/0411174v3 (Theorem 1.1 and Lemma 3.15 of arXiv:math/0411174v3).
