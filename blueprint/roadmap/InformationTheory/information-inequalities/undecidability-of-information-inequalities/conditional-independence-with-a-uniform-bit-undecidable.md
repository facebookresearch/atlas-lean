# Conditional independence constraints with one uniform bit are undecidable

No algorithm decides whether finitely many conditional independence statements can hold together with one variable being a fair coin, nor whether they imply that a variable of bounded cardinality is constant; so conditional independence implication with a single cardinality constraint is undecidable.

For random variables $X_1, \dots, X_n$ with finite support and $A \subseteq \{1, \dots, n\}$ write $X_A$ for the subtuple; the statement $I(X_A; X_B \mid X_C) = 0$ says that $X_A$ and $X_B$ are [conditionally independent](../../../Probability/random-fields/conditional-independence-on-finite-configuration/cond-indep.md) given $X_C$, in terms of [conditional mutual information](../../entropy-and-mutual-information/conditional-mutual-information/finite-conditional-mutual-information.md).

**Theorem (Li).**

1. It is undecidable, given $n$, $m$ and $A_j, B_j, C_j \subseteq \{1, \dots, n\}$ for $j = 1, \dots, m$, whether there are random variables $X_1, \dots, X_n$ with finite support such that $I(X_{A_j}; X_{B_j} \mid X_{C_j}) = 0$ for all $j$ and $X_1$ is uniformly distributed on two values (Theorem 2 of the source).
2. For every fixed integer $r \ge 2$ it is undecidable, given such data, whether $I(X_{A_j}; X_{B_j} \mid X_{C_j}) = 0$ for all $j$ together with $|\mathrm{supp}\, X_1| \le r$ implies $H(X_1) = 0$ (Corollary 3), and this remains undecidable when the sets $A_j, B_j, C_j$ are pairwise disjoint for each $j$ and the conclusion is $I(X_1; X_2) = 0$ (Corollary 5).

Without any cardinality constraint, the conditional independence implication problem was later shown undecidable by the same author: [conditional independence implication is undecidable](conditional-independence-implication-is-undecidable.md) (IEEE Trans. Inform. Theory 69 (2023) 3493–3510). If every variable has bounded cardinality the implication problem is decidable.

## Depends on

- [Conditional independence for a finite weight](../../../Probability/random-fields/conditional-independence-on-finite-configuration/cond-indep.md)
- [Conditional mutual information of a finite joint law](../../entropy-and-mutual-information/conditional-mutual-information/finite-conditional-mutual-information.md)

## Proof depends on

None.

## Expansion

The proof reuses the periodic tiling construction behind [the undecidability of affine entropic constraints](affine-entropic-constraints-are-undecidable.md), checking that it uses only conditional independence constraints and constraints forcing variables to be uniform on $2$, $3$, $4$ or $105$ values, and replaces the latter by conditional independence constraints and a single uniform bit. Corollary 3 bounds cardinalities through rational approximations of $\log 3$, and the disjoint form (Corollary 5) uses a polynomial-time reduction from general to disjoint conditional independence statements via perfectly resolvable pairs (Theorem 4 of the source). The periodic tiling theorem of Gurevich and Koryakov and these constructions have no pages.

## Sources

- C. T. Li, "The undecidability of conditional affine information inequalities and conditional independence implication with a binary constraint", IEEE Transactions on Information Theory 68 (2022), no. 12, 7685–7701, https://doi.org/10.1109/TIT.2022.3190800; read in arXiv:2104.05634v4 (Theorem 2 and its proof, Corollaries 3 and 5, and Theorem 4 of arXiv:2104.05634v4).
