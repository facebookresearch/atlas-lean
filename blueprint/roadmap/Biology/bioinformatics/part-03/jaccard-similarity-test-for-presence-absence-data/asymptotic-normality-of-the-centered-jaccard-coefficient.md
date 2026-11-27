# Asymptotic normality of the centered Jaccard coefficient

**Setting.** As in the [null expectation of the Jaccard coefficient](null-expectation-of-the-jaccard-coefficient.md), let $y_i, y_j \in \{0,1\}^m$ be independent presence–absence vectors with i.i.d. $\mathrm{Bernoulli}(p_i)$ and $\mathrm{Bernoulli}(p_j)$ coordinates, and put

$$q_1 = p_i p_j, \qquad q_2 = p_i + p_j - 2 p_i p_j,$$

the probabilities that a feature is present in both vectors and in exactly one of them. Let $T^c = T(y_i, y_j) - q_1/(q_1 + q_2)$ be the centered Jaccard coefficient.

**Proposition.** With $p_i, p_j \in (0,1)$ known, as $m \to \infty$,

$$\sqrt{m}\, T^c(y_i, y_j) \xrightarrow{d} \mathcal{N}(0, \sigma^2), \qquad \sigma^2 = \frac{q_1 q_2}{(q_1 + q_2)^3}.$$

Hence, for known marginals, $2\,\Phi\bigl(-\sqrt{m}\,|T^c(y_i, y_j)|/\sigma\bigr)$, where $\Phi$ is the standard normal distribution function, is an asymptotic two-sided p-value for the null hypothesis of independent occurrence.

For example, $p_i = p_j = 1/2$ gives $q_1 = 1/4$, $q_2 = 1/2$ and $\sigma^2 = 8/27$. The source's Proposition 2 states $\sigma^2 = q_1 q_2 (1 - q_2)/(q_1 + q_2)^3$, which differs by the factor $1 - q_2$; the multinomial covariance below gives the expression above. The statement covers only the known-marginal statistic: centring at $\hat q_1/(\hat q_1 + \hat q_2)$ computed from the same observations changes the limit law at first order, and its variance is not this $\sigma^2$.

## Depends on

- [Null expectation of the Jaccard coefficient](null-expectation-of-the-jaccard-coefficient.md)

## Proof depends on

- [Central limit theorem for multinomial proportions](../../../../Probability/central-limit-theorems/multivariate-central-limit-theorem/clt-for-multinomial-proportions.md)
- [Delta method](../../../../Probability/convergence-of-measures/slutsky-s-theorem-and-the-delta-method/delta-method.md)

## Expansion

The pair $(N_1, N_2 + N_3)/m$ is a multinomial proportion vector with mean $(q_1, q_2)$, so by the multinomial central limit theorem $\sqrt{m}\,[(N_1, N_2+N_3)/m - (q_1, q_2)] \to \mathcal{N}(0, \Sigma)$ with $\Sigma = \begin{pmatrix} q_1(1-q_1) & -q_1 q_2 \\ -q_1 q_2 & q_2(1-q_2) \end{pmatrix}$. Apply the delta method to $g(x_1, x_2) = x_1/(x_1 + x_2)$, whose gradient is $\nabla g = \bigl(x_2, -x_1\bigr)/(x_1 + x_2)^2$; at $(q_1, q_2)$ the quadratic form is $\nabla g\, \Sigma\, \nabla g^{\mathsf T} = q_1 q_2\bigl[q_2(1 - q_1) + 2 q_1 q_2 + q_1(1 - q_2)\bigr]/(q_1 + q_2)^4 = q_1 q_2/(q_1 + q_2)^3$.

## Sources

- N. C. Chung, B. Miasojedow, M. Startek and A. Gambin, "Jaccard/Tanimoto similarity test and estimation methods for biological presence-absence data", *BMC Bioinformatics* (2019), Methods, Proposition 2 (whose variance simplification is corrected here). <https://doi.org/10.1186/s12859-019-3118-5> (PMC6929325)
