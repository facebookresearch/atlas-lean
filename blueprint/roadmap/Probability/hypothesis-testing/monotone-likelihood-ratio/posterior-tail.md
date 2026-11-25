# Posterior tail probability

Let $\mu$ be a measure on $\mathbb{R}$ (the prior), $L : \mathbb{N} \times \mathbb{R} \to \mathbb{R}$ a likelihood family, $n \in \mathbb{N}$ and $t \in \mathbb{R}$. The posterior tail probability of $\{\theta > t\}$ after observing $n$ is given by Bayes' formula,

$$\Pi(\theta > t \mid n) = \frac{\int_{\theta > t} L(n, \theta)\, d\mu(\theta)}{\int L(n, \theta)\, d\mu(\theta)}.$$

When the marginal likelihood $\int L(n, \cdot)\, d\mu$ is $0$ the value is $0$ by convention (division by zero). In particular it is $0$ when $L(n, \cdot)$ is not $\mu$-integrable: the denominator is then $0$ by the convention for non-integrable functions, while the numerator, an integral over $\{\theta > t\}$ only, may be nonzero. It is a genuine posterior probability only when $L$ is nonnegative and the marginal likelihood is positive: a signed $L$ can give a value outside $[0, 1]$.
