# Asymptotic normality of the centered Jaccard coefficient

**Setting.** As in the [null expectation of the Jaccard coefficient](null-expectation-of-the-jaccard-coefficient.md), let $y_i, y_j \in \{0,1\}^m$ be independent presence–absence vectors with i.i.d. $\mathrm{Bernoulli}(p_i)$ and $\mathrm{Bernoulli}(p_j)$ coordinates, and put

$$q_1 = p_i p_j, \qquad q_2 = p_i + p_j - 2 p_i p_j,$$

the probabilities that a feature is present in both vectors and in exactly one of them. Let $T^c = T(y_i, y_j) - q_1/(q_1 + q_2)$ be the centered Jaccard coefficient.

**Proposition.** As $m \to \infty$,

$$\sqrt{m}\, T^c(y_i, y_j) \xrightarrow{d} \mathcal{N}(0, \sigma^2), \qquad \sigma^2 = \frac{q_1 q_2 (1 - q_2)}{(q_1 + q_2)^3}.$$

Replacing $p_i, p_j$ by the plug-in estimates $\hat p_i = \#\{k : y_{ik} = 1\}/m$, $\hat p_j = \#\{k : y_{jk} = 1\}/m$ in $q_1, q_2, \sigma$ gives the asymptotic two-sided p-value

$$2\,\Phi\!\left(-\frac{\sqrt{m}}{\hat\sigma}\left|T(y_i, y_j) - \frac{\hat q_1}{\hat q_1 + \hat q_2}\right|\right),$$

where $\Phi$ is the standard normal distribution function.

## Depends on

- [Null expectation of the Jaccard coefficient](null-expectation-of-the-jaccard-coefficient.md)

## Expansion

The pair $(N_1, N_2 + N_3)/m$ is a multinomial proportion vector with mean $(q_1, q_2)$, so by the multinomial central limit theorem $\sqrt{m}\,[(N_1, N_2+N_3)/m - (q_1, q_2)] \to \mathcal{N}(0, \Sigma)$ with $\Sigma = \begin{pmatrix} q_1(1-q_1) & -q_1 q_2 \\ -q_1 q_2 & q_2(1-q_2) \end{pmatrix}$. Apply the delta method to $g(x_1, x_2) = x_1/(x_1 + x_2)$, whose gradient is $\nabla g = \bigl(x_2, -x_1\bigr)/(x_1 + x_2)^2$; the quadratic form $\nabla g\, \Sigma\, \nabla g^{\mathsf T}$ at $(q_1, q_2)$ simplifies to $\sigma^2$.

## Sources

- N. C. Chung, B. Miasojedow, M. Startek and A. Gambin, "Jaccard/Tanimoto similarity test and estimation methods for biological presence-absence data", *BMC Bioinformatics* (2019), Methods, Proposition 2 and Eq. (6). <https://doi.org/10.1186/s12859-019-3118-5> (PMC6929325)
