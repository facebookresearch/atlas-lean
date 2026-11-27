# Chen–Stein Poisson approximation: two moments suffice

Let $(X_\alpha)_{\alpha \in I}$ be [Bernoulli random variables](../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/is-bernoulli-rv.md) with $p_\alpha = EX_\alpha > 0$, $W = \sum_\alpha X_\alpha$ and $\lambda = EW \in (0, \infty)$, and choose for each $\alpha$ a neighbourhood of dependence $B_\alpha \ni \alpha$. Define $b_1 = \sum_\alpha\sum_{\beta \in B_\alpha} p_\alpha p_\beta$, $b_2 = \sum_\alpha\sum_{\beta \in B_\alpha, \beta \ne \alpha} E[X_\alpha X_\beta]$, $b_3 = \sum_\alpha E\bigl|E[X_\alpha - p_\alpha \mid \sigma(X_\beta : \beta \in I \setminus B_\alpha)]\bigr|$, using the [conditional expectation](../../../Probability/foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/conditional-expectation.md) given the whole configuration outside $B_\alpha$, and $b'_3 = \sum_\alpha E\bigl|E[X_\alpha - p_\alpha \mid \sum_{\beta \in I \setminus B_\alpha} X_\beta]\bigr|$, which conditions only on the number of occurrences outside $B_\alpha$ (Arratia, Goldstein and Gordon 1989, pp. 10–11). Since that sum is a function of the outside configuration, conditional Jensen gives $b'_3 \le b_3$, and the inequality can be strict. With $Z$ Poisson with mean $\lambda$, the source measures distance by the norm $\|\mathcal L(W) - \mathcal L(Z)\| = \sup_{\|h\| = 1}|Eh(W) - Eh(Z)| = 2\sup_A|P(W \in A) - P(Z \in A)|$, which is twice the [total variation distance](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md) $d_{TV}(\mathcal L(W), \mathcal L(Z))$. Arratia, Goldstein and Gordon (1989, Theorem 1) prove the scalar bounds with $b'_3$:

$$\|\mathcal L(W) - \mathcal L(Z)\| \le 2\Bigl[(b_1 + b_2)\frac{1 - e^{-\lambda}}{\lambda} + b'_3\,(1 \wedge 1.4\lambda^{-1/2})\Bigr] \le 2(b_1 + b_2 + b'_3)$$

and, for the zero event, the refined bound $|P(W = 0) - e^{-\lambda}| \le (b_1 + b_2 + b'_3)\frac{1 - e^{-\lambda}}{\lambda}$, with the coarser consequence $|P(W = 0) - e^{-\lambda}| \le (1 \wedge \lambda^{-1})(b_1 + b_2 + b'_3)$. Because $b'_3 \le b_3$, all of these also hold with $b_3$ in place of $b'_3$. Their Theorem 2 gives the process version, which uses $b_3$: in the same norm, the distance between the law of $(X_\alpha)_{\alpha \in I}$ and that of independent Poisson variables with means $p_\alpha$ is at most $2(2b_1 + 2b_2 + b_3)$.

## Depends on

- [Total variation distance between finite measures](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)
- [Poisson law as a probability measure](poisson-prob-measure.md)
- [Bernoulli random variable](../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/is-bernoulli-rv.md)
- [Conditional expectation given a σ-field](../../../Probability/foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/conditional-expectation.md)

## Expansion

1. The setting: dependent Bernoulli variables, neighbourhoods of dependence, and the quantities $b_1, b_2, b_3, b'_3$ (neighbourhood size, expected number of neighbouring occurrences, and dependence on the outside configuration or only on the outside count), with $b'_3 \le b_3$.
2. Stein's equation for the Poisson law and the bounds on its solution, with the factors $(1 - e^{-\lambda})/\lambda$ and $1 \wedge 1.4\lambda^{-1/2}$ (Lemma 1).
3. Theorem 1 with $b'_3$, from the local decomposition $W = X_\alpha + \sum_{\beta \in B_\alpha\setminus\{\alpha\}} X_\beta + \sum_{\beta \notin B_\alpha} X_\beta$ in Section 5, and the refined bound for $P(W = 0)$ with its coarser consequence.
4. Theorem 2 via the finite-dimensional bound for a partition of $I$, and the comparison with independent events (Theorem 3).
5. Applications to sequence matching and other examples in the source, as separate statements; independent trials recover [Poisson convergence in law (binomial approximation)](../../../Probability/central-limit-theorems/poisson-limit-theorem/tendsto-binomial-poisson-approx.md) as a special case.

## Sources

- R. Arratia, L. Goldstein and L. Gordon, Two moments suffice for Poisson approximations: the Chen–Stein method, Ann. Probab. 17 (1989), 9–25, Theorems 1 and 2. <https://doi.org/10.1214/aop/1176991491>
