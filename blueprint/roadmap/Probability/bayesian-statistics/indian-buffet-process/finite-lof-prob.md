# Closed-form lof-class probability of the finite feature model

Let $\alpha \in \mathbb{R}$, $K, N \in \mathbb{N}$, and let $Z$ be a binary matrix with $N$ rows and $K_+$ columns, with [feature counts](feature-count.md) $m_k$ and [history counts](history-count.md) $K_h$. The finite-model class probability is

$$\frac{\alpha^{K_+}}{\prod_h K_h!} \cdot \frac{K!}{K_0!\, K^{K_+}} \cdot \Big(\frac{N!}{\prod_{j=1}^{N} (j + \alpha/K)}\Big)^K \cdot \prod_{k=1}^{K_+} \frac{(N - m_k)! \prod_{j=1}^{m_k - 1} (j + \alpha/K)}{N!}, \qquad K_0 = K - K_+,$$

where $K!/K_0! = K(K-1)\cdots(K - K_+ + 1)$ is the falling factorial (so the expression is $0$ when $K < K_+$), $\alpha/K$ is read as $0$ and a division by $0$ as $0$ when $K = 0$, and for a zero column ($m_k = 0$) the inner product is empty. The third factor is the [empty-column factor](empty-columns-factor.md).

Griffiths and Ghahramani (2011, Equation 12, rewritten as in Equation 13) give it as the probability, in the finite feature model with $K$ features ($\pi_k \sim \mathrm{Beta}(\alpha/K, 1)$ and, given $\pi_k$, independent $\mathrm{Bernoulli}(\pi_k)$ entries in column $k$), of the lof-equivalence class whose non-empty columns are those of $Z$; the intended input has every column non-empty. The definition is that closed form; its derivation from the beta–Bernoulli model (integrating out each $\pi_k$, Equation 10, and counting the matrices in a class) is in the source.

## Informally uses

- [The beta-binomial distribution](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/conjugate-priors/binomial-kernel-comp-beta-measure.md): integrating $\pi_k^{m_k} (1 - \pi_k)^{N - m_k}$ against $\mathrm{Beta}(\alpha/K, 1)$ gives the probability of one column, the step from which the paper derives the closed form (Griffiths and Ghahramani 2011, Equation 10).

## Sources

- Thomas L. Griffiths and Zoubin Ghahramani, *The Indian buffet process: an introduction and review*, J. Mach. Learn. Res. 12 (2011), 1185–1224, Equations 10, 12 and 13.
