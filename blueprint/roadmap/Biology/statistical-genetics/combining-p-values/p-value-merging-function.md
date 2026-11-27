# p-value merging functions

A **p-variable** is a random variable $P$ that is a [valid p-value](../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md) under the underlying probability measure, $\mathbb P(P \le \epsilon) \le \epsilon$ for all $\epsilon \in (0, 1)$ (Eq. (4) of the source). A **merging function** is an increasing Borel function $F : [0, 1]^K \to [0, \infty)$ such that $F(U_1, \dots, U_K)$ is a p-variable for every family $U_1, \dots, U_K$ of uniform random variables on $[0, 1]$ on a common probability space, with arbitrary dependence; equivalently, for each $\epsilon \in (0, 1)$,

$$\sup\{\mathbb P(F(U_1, \dots, U_K) \le \epsilon) : U_1, \dots, U_K \text{ uniform}\} \le \epsilon. \tag{5}$$

$F$ is **precise** if equality holds in (5) for every $\epsilon$ (Eq. (6)). A family $(F_K)_{K \ge 2}$ is **asymptotically precise** if for every $a \in (0, 1)$, $a F_K$ fails to be a merging function for all large enough $K$.

If $F$ is a merging function and $P_1, \dots, P_K$ are p-variables on one probability space, then $F(P_1, \dots, P_K)$ is a p-variable. The classical example is the Bonferroni function $K \min(p_1, \dots, p_K)$.

## Depends on

- [Valid p-value](../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md)

## Expansion

For the last claim, each p-variable $P_k$ dominates a uniform variable $U_k = \mathbb P(P_k < P_k(\omega)) + \Theta(\omega)\, \mathbb P(P_k = P_k(\omega))$ built with an independent uniform $\Theta$; since $F$ is increasing, $F(P) \ge F(U)$ pointwise, so $\mathbb P(F(P) \le \epsilon) \le \mathbb P(F(U) \le \epsilon) \le \epsilon$ (Section 2). Lemma 1 of the source restates (5) as a lower bound on the smallest left $\epsilon$-quantile of $F(U_1, \dots, U_K)$ over all dependence structures, which connects merging functions to robust risk aggregation.

## Sources

- V. Vovk and R. Wang, Combining p-values via averaging, Biometrika 107 (2020). <https://doi.org/10.1093/biomet/asaa027>; numbering follows the preprint <https://arxiv.org/abs/1212.4966> (version 5).
