# Risk of the James–Stein estimator

For $p \ge 3$ and $X \sim \mathcal N_p(\theta, I)$, $\|X\|^{-2}$ is integrable and the [James–Stein estimator](james-stein.md) has quadratic risk

$$\mathbb E\, \|\delta(X) - \theta\|^2 = p - (p - 2)^2\, \mathbb E\, \|X\|^{-2}$$

for every $\theta$. This is Johnstone's draft, equation (2.64). The condition $p \ge 3$ is what makes $\mathbb E \|X\|^{-2}$ finite (Johnstone, equation (2.67)); for $p \le 2$ it is infinite for every $\theta$.

## Informally uses

- [Stein's unbiased risk estimate](integral-sum-sq-add-sub-pi-gaussian-real.md): Johnstone obtains (2.64) by applying (2.61) to $g(x) = -(p - 2) x / \|x\|^2$, whose divergence is $-(p - 2)^2 / \|x\|^2$.

## Sources

- I. M. Johnstone, *Gaussian Estimation: Sequence and Wavelet Models*, pre-publication draft of 16 September 2019, https://imjohnstone.su.domains/GE_09_16_19.pdf. Numbers refer to that draft.
- W. James and C. Stein, "Estimation with quadratic loss", *Proc. Fourth Berkeley Symp. Math. Statist. Probab.*, Vol. 1 (1961) 361–379 (cited for attribution; not consulted for numbering).
