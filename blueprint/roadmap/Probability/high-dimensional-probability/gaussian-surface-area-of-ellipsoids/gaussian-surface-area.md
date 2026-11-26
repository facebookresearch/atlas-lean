# Gaussian surface area

Let $n \in \mathbb{N}$, let $\gamma_n$ be the standard Gaussian measure on $\mathbb{R}^n$, and let $A \subseteq \mathbb{R}^n$ be any set. For $\delta > 0$ write $A_\delta = \{x : \operatorname{dist}(x, A) \le \delta\}$ for the closed $\delta$-thickening of $A$. The Gaussian surface area of $A$ is

$$\Gamma(A) = \liminf_{\delta \to 0^+} \frac{\gamma_n(A_\delta \setminus A)}{\delta} \in [0, \infty],$$

computed in the extended nonnegative reals, so that it is always defined and may equal $+\infty$. Since $A$ need not be measurable, $\gamma_n$ is evaluated as an outer measure; when $A$ is a Borel set, $A_\delta \setminus A$ is Borel and $\gamma_n(A_\delta \setminus A)$ is its ordinary Gaussian measure.
