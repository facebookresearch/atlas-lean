# A finitely presented group with solvable conjugacy problem and unsolvable twisted conjugacy problem

There is a finitely presented group whose conjugacy problem is solvable while its twisted conjugacy problem is not; consequently there are finitely presented groups $G$ with solvable conjugacy problem and automorphisms $\varphi$ for which $G \rtimes_\varphi \mathbb{Z}$ has unsolvable conjugacy problem.

1. There exists a finitely presented group $G$ with solvable conjugacy problem $\mathrm{CP}(G)$ and unsolvable twisted conjugacy problem $\mathrm{TCP}(G)$ (Corollary 4.9 of the source).
2. There exist a finitely presented group $G$ and $\varphi \in \mathrm{Aut}(G)$ such that $\mathrm{CP}(G)$ is solvable and $\mathrm{CP}(G \rtimes_\varphi \mathbb{Z})$ is unsolvable; conversely, there exist a finitely presented group $G$ and $\varphi \in \mathrm{Aut}(G)$ such that $\mathrm{CP}(G \rtimes_\varphi \mathbb{Z})$ is solvable and $\mathrm{CP}(G)$ is unsolvable (Corollary 4.10).

## Depends on

- [Twisted conjugacy problem](twisted-conjugacy-problem.md)
- [Group](../../../group-basics/group.md)
- [Solvable conjugacy problem for a quotient of a free group](../../decision-problems-in-free-abelianized-extensions/conjugacy-problem-solvable.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Gorjaga and Kirkinskii, and Collins and Miller, gave finitely presented groups $F$ with an index-two subgroup $G$ such that $\mathrm{CP}(G)$ is solvable and $\mathrm{CP}(F)$ is not. For a normal subgroup of finite index, a solution of the twisted conjugacy problem of the subgroup would solve the conjugacy problem of the larger group (Proposition 4.7 of the source), so $\mathrm{TCP}(G)$ is unsolvable. Then some automorphism $\varphi$ has $\mathrm{TCP}_\varphi(G)$ unsolvable, which makes $\mathrm{CP}(G \rtimes_\varphi \mathbb{Z})$ unsolvable; the converse uses the Collins–Miller example with an order-two automorphism.

## Sources

- O. Bogopolski, A. Martino and E. Ventura, "Orbit decidability and the conjugacy problem for some extensions of groups", Transactions of the American Mathematical Society 362 (2010), no. 4, 2003–2036, https://doi.org/10.1090/S0002-9947-09-04817-X; read in arXiv:0712.3104v1 (Corollaries 4.9 and 4.10 of arXiv:0712.3104v1).
