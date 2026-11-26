# Positivity

Let $\mu$ be a measure on a measurable space $\Omega$, $R \subseteq \Omega$ the response event and $X : \Omega \to \mathcal X$ a covariate. Response positivity holds if there is $\varepsilon > 0$ such that for every $x \in \mathcal X$ with $\mu(X = x) \ne 0$, where $\mu(X = x) \in [0, \infty]$ is the measure itself,

$$\varepsilon \le \frac{\mu_{\mathbb R}(R \cap \{X = x\})}{\mu_{\mathbb R}(X = x)}.$$

Here $\mu_{\mathbb R}(A)$ is the real number $\mu(A)$ when $\mu(A) < \infty$ and $0$ when $\mu(A) = \infty$, and $x / 0 = 0$. In particular a value $x$ with $\mu(X = x) = \infty$ is tested, and its ratio is $0$, so positivity then fails.
