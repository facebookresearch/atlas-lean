# Conditional independence constraints with one uniform bit are undecidable

No algorithm decides whether finitely many conditional independence statements can hold together with one variable being a fair coin, nor whether they imply that a variable of bounded cardinality is constant; so conditional independence implication with a single cardinality constraint is undecidable.

As in the source, random variables are discrete (countably many values) with finite entropies, and entropies are in bits: a discrete random tuple with distribution $p$ has entropy $H = -\sum_x p(x) \log_2 p(x)$, which for a finitely supported $p$ is the [Shannon entropy](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md) of $p$. For jointly distributed such $X_1, \dots, X_n$ and $A \subseteq \{1, \dots, n\}$ write $X_A$ for the subtuple, and let

$$
I(X_A; X_B \mid X_C) = H(X_{A \cup C}) + H(X_{B \cup C}) - H(X_{A \cup B \cup C}) - H(X_C),
$$

the conditional mutual information, which for finitely supported variables is the [conditional mutual information of a finite joint law](../../entropy-and-mutual-information/conditional-mutual-information/finite-conditional-mutual-information.md); $I(X_A; X_B \mid X_C) = 0$ says that $X_A$ and $X_B$ are [conditionally independent](../../../Probability/random-fields/conditional-independence-on-finite-configuration/cond-indep.md) given $X_C$.

**Theorem (Li).** It is undecidable, given $n$, $m$ and $A_j, B_j, C_j \subseteq \{1, \dots, n\}$ for $j = 1, \dots, m$, whether there are jointly distributed discrete random variables $X_1, \dots, X_n$ with finite entropies such that $I(X_{A_j}; X_{B_j} \mid X_{C_j}) = 0$ for all $j$ and $X_1$ is uniformly distributed on two values (Theorem 2 of the source).

The source deduces that for every fixed integer $r \ge 2$ it is undecidable, given such data, whether $I(X_{A_j}; X_{B_j} \mid X_{C_j}) = 0$ for all $j$ together with $|\mathrm{supp}\, X_1| \le r$ implies $H(X_1) = 0$ (Corollary 3), and that this remains undecidable when the sets $A_j, B_j, C_j$ are pairwise disjoint for each $j$, $n \ge 2$, and the conclusion is $I(X_1; X_2) = 0$ (Corollary 5). Without any cardinality constraint, the conditional independence implication problem was later shown undecidable by the same author: [conditional independence implication is undecidable](conditional-independence-implication-is-undecidable.md) (IEEE Trans. Inform. Theory 69 (2023) 3493–3510). If every variable has bounded cardinality the implication problem is decidable.

## Depends on

- [Shannon entropy](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)
- [Conditional independence for a finite weight](../../../Probability/random-fields/conditional-independence-on-finite-configuration/cond-indep.md)
- [Conditional mutual information of a finite joint law](../../entropy-and-mutual-information/conditional-mutual-information/finite-conditional-mutual-information.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reuses the periodic tiling construction behind [the undecidability of affine entropic constraints](affine-entropic-constraints-are-undecidable.md), checking that it uses only conditional independence constraints and constraints forcing variables to be uniform on $2$, $3$, $4$ or $105$ values, and replaces the latter by conditional independence constraints and a single uniform bit. Corollary 3 bounds cardinalities through rational approximations of $\log 3$, and the disjoint form (Corollary 5) uses a polynomial-time reduction from general to disjoint conditional independence statements via perfectly resolvable pairs (Theorem 4 of the source). The variables these constructions build from a periodic tiling are finitely supported. A good expansion links pages for the undecidability of the periodic tiling problem (Gurevich and Koryakov), the replacement of uniformity constraints by conditional independence constraints, and the reduction to disjoint statements.

## Sources

- C. T. Li, "The undecidability of conditional affine information inequalities and conditional independence implication with a binary constraint", IEEE Transactions on Information Theory 68 (2022), no. 12, 7685–7701, https://doi.org/10.1109/TIT.2022.3190800; read in arXiv:2104.05634v4 (the notations, Section II on the class of random variables, Theorem 2 and its proof in Section V, Corollaries 3 and 5, and Theorem 4 of arXiv:2104.05634v4).
