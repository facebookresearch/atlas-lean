# The domino problem under horizontal constraints is undecidable exactly when the constraints allow a non-periodic row

For a fixed one-dimensional subshift of finite type $H$, deciding whether a two-dimensional subshift of finite type whose rows all lie in $H$ is empty is possible exactly when every point of $H$ is periodic; otherwise the problem is undecidable.

Let $\mathcal{A}$ be a finite alphabet and $H \subseteq \mathcal{A}^{\mathbb{Z}}$ a one-dimensional SFT, fixed beforehand. For a finite set $\mathcal{F}$ of forbidden finite patterns over $\mathcal{A}$ in $\mathbb{Z}^2$, the subshift $X_{\mathcal{F}}$ *with added horizontal constraints from $H$* is

$$
X_{H,\mathcal{F}} = \{ x \in X_{\mathcal{F}} : (x_{k,j})_{k \in \mathbb{Z}} \in H \text{ for every } j \in \mathbb{Z} \},
$$

the two-dimensional SFT defined by $\mathcal{F}$ in which every row is a point of $H$. The *domino problem under horizontal constraints* $H$ is the set

$$
\mathrm{DP}_h(H) = \{ \langle \mathcal{F} \rangle : X_{H,\mathcal{F}} \ne \emptyset \},
$$

where $\langle \mathcal{F} \rangle$ is an encoding of the finite set $\mathcal{F}$; the input is $\mathcal{F}$ alone, and $H$ is a parameter.

**Theorem.** $\mathrm{DP}_h(H)$ is decidable if and only if every point of $H$ is periodic (Proposition 2.2 of the source). Thus, if $H$ contains a point that is not periodic, $\mathrm{DP}_h(H)$ is undecidable.

## Depends on

- [Subshifts of finite type on a finitely generated group and the domino problem](subshifts-of-finite-type-on-groups.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

If $H$ has a non-periodic point, its Rauzy graph has a vertex with two distinct paths from it to itself, and suitable concatenations of them give finitely many words $U_1, \dots, U_n$ of equal length that can be juxtaposed freely and parsed uniquely. Given any two-dimensional SFT $Y$ on an alphabet $\{T_1, \dots, T_n\}$, one adds finitely many forbidden patterns $\mathcal{F}$ forcing every row to be a concatenation of the words $U_k$, aligned vertically, with the pattern of indices a configuration of $Y$; then $X_{H,\mathcal{F}}$ is a root of $Y$ (Proposition 2.1), and in particular $X_{H,\mathcal{F}}$ is empty exactly when $Y$ is. This reduces the domino problem of $\mathbb{Z}^2$, undecidable by Berger, to $\mathrm{DP}_h(H)$. If every point of $H$ is periodic, with common period $p$, the algorithm searches rectangles of width a multiple of $p$ and bounded height that respect the local rules and can be juxtaposed horizontally with themselves; by the pigeonhole principle either none exists, and $X_{H,\mathcal{F}}$ is empty, or one contains a repeated block and yields a doubly periodic configuration.

When the added rules are required to be vertical, so that the question is whether $H$ and a one-dimensional SFT $V$ given as input combine into a non-empty two-dimensional subshift, the source characterizes the nearest-neighbor $H$ for which this problem is decidable by a graph condition (condition D) on the Rauzy graph of $H$ (Theorem 5.2).

## Sources

- S. J. Esnay and M. Sablik, "Parametrization by horizontal constraints in the study of algorithmic properties of $\mathbb{Z}^2$-subshifts of finite type", Discrete and Continuous Dynamical Systems 43 (2023), no. 5, 2002–2046, https://doi.org/10.3934/dcds.2023001; read in arXiv:2203.00434v2 (the definition of $X_{H,\mathcal{F}}$ in Section 1, the definition of $\mathrm{DP}_h(H)$, Propositions 2.1 and 2.2 in Section 2, and Theorem 5.2 of arXiv:2203.00434v2).
