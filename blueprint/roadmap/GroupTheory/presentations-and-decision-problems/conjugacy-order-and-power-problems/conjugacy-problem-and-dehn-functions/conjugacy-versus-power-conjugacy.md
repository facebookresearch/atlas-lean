# The conjugacy and power conjugacy problems are independent

There is a finitely presented group with quadratic Dehn function whose conjugacy problem is undecidable but whose power conjugacy problem is decidable, and a finitely presented group whose power conjugacy problem is undecidable but whose conjugacy problem is decidable.

For a group $G = \langle X \mid R \rangle$, the power conjugacy problem asks for an algorithm that decides, given words $u, v$ over $X^{\pm 1}$, whether there are non-zero integers $k, l$ such that $u^k$ is conjugate to $v^l$ in $G$. Then (Theorem 1.3 of the source):

1. there is a finitely presented group $G$ with undecidable conjugacy problem and decidable power conjugacy problem, and $G$ can be taken with quadratic Dehn function;
2. there is a finitely presented group $H$ with undecidable power conjugacy problem and decidable conjugacy problem.

## Depends on

- [Group](../../../group-basics/group.md)
- [Solvable conjugacy problem for a quotient of a free group](../../decision-problems-in-free-abelianized-extensions/conjugacy-problem-solvable.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [A finitely presented group with quadratic Dehn function and undecidable conjugacy problem](quadratic-dehn-undecidable-conjugacy.md)

## Expansion

For clause 1, the group $G$ is built from an $S$-machine with non-recursive language of accepted inputs, which gives undecidable conjugacy problem and quadratic Dehn function (Lemmas 3.21 and 4.2 of the source). To decide whether $U^k$ and $V^l$ are conjugate for some non-zero exponents $k, l$, one may assume that $U$ and $V$ have infinite order (Lemma 7.1); the exponents can then be bounded recursively in terms of $U$ and $V$ (Lemmas 7.3, 7.6 and 7.7), and conjugacy of elements of infinite order is decidable in $G$ (Theorem 1.4). Clause 2 uses no $S$-machine. It starts from McCool's group

$$
\Pi_2 = \langle y_n, z_n \ (n \ge 1) \mid y_n z_n = z_n y_n,\ y_{\phi(n)} = z_{\phi(n)}^{\,n} \ (n \ge 1) \rangle,
$$

with $\phi$ a recursive one-to-one function with non-recursive range, which also appears on the page [a finitely presented group with solvable word problem and unsolvable order and power problems](../order-and-power-problems/solvable-word-problem-unsolvable-order-power.md); $\Pi_2$ has decidable word and conjugacy problems, and some powers of $y_r$ and $z_r$ are conjugate exactly when $r$ is in the range of $\phi$, so its power conjugacy problem is undecidable. A theorem of Olshanskii and Sapir embeds $\Pi_2$ in a $2$-generated group $K$ with decidable conjugacy problem, with the Frattini property that two elements of $\Pi_2$ are conjugate in $K$ exactly when they are conjugate in $\Pi_2$; and $K$ Frattini embeds in a finitely presented group $H$ with decidable conjugacy problem, in which the power conjugacy problem is therefore undecidable. A good expansion adds and links pages for these two Frattini embedding theorems and for the conjugacy decision for elements of infinite order (Theorem 1.4).

## Sources

- A. Yu. Olshanskii and M. V. Sapir, "Algorithmic problems in groups with quadratic Dehn function", Groups, Geometry, and Dynamics 16 (2022), no. 4, 1289–1339, https://doi.org/10.4171/GGD/694; read in arXiv:2012.10417v1 (Theorem 1.3 with its proof in Section 7, Theorem 1.4 and Lemmas 7.1, 7.3, 7.6 and 7.7 of arXiv:2012.10417v1).
