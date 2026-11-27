# The conjugacy and power conjugacy problems are independent

There is a finitely presented group with quadratic Dehn function whose conjugacy problem is undecidable but whose power conjugacy problem is decidable, and a finitely presented group whose power conjugacy problem is undecidable but whose conjugacy problem is decidable.

For a group $G = \langle X \mid R \rangle$, the power conjugacy problem asks for an algorithm that decides, given words $u, v$ over $X^{\pm 1}$, whether there are non-zero integers $k, l$ such that $u^k$ is conjugate to $v^l$ in $G$. Then (Theorem 1.3 of the source):

1. there is a finitely presented group $G$ with undecidable conjugacy problem and decidable power conjugacy problem, and $G$ can be taken with quadratic Dehn function;
2. there is a finitely presented group $H$ with undecidable power conjugacy problem and decidable conjugacy problem.

## Depends on

- [Group](../../../group-basics/group.md)
- [Solvable conjugacy problem for a quotient of a free group](../../decision-problems-in-free-abelianized-extensions/conjugacy-problem-solvable.md)

## Proof depends on

- [A finitely presented group with quadratic Dehn function and undecidable conjugacy problem](quadratic-dehn-undecidable-conjugacy.md)

## Expansion

Clause 1 refines the authors' group with quadratic Dehn function and undecidable conjugacy problem so that non-trivial powers of elements have decidable conjugacy, using $S$-machine constructions. Clause 2 uses an $S$-machine whose accepted inputs are encoded by conjugacy of powers, while conjugacy of the elements themselves stays decidable.

## Sources

- A. Yu. Olshanskii and M. V. Sapir, "Algorithmic problems in groups with quadratic Dehn function", Groups, Geometry, and Dynamics 16 (2022), no. 4, 1289–1339, https://doi.org/10.4171/GGD/694; read in arXiv:2012.10417v1 (Theorem 1.3 of arXiv:2012.10417v1).
