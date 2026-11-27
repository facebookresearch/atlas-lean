# Stochastic growth rate of a dispersing population in randomly fluctuating patches

Let $\mathbf X_t = (X^1_t,\dots,X^n_t)^\top$ be abundances in $n$ patches with mean per-capita growth rates $\mu = (\mu_i)$, environmental noise covariance $\Sigma = \Gamma^\top\Gamma$, and a dispersal matrix $D$ (nonnegative off-diagonal entries $D_{ij}$, the per-capita rate of moving from $i$ to $j$, and zero row sums):

$$d\mathbf X_t = \mathrm{diag}(\mathbf X_t)\big(\mu\,dt + \Gamma^\top d\mathbf B_t\big) + D^\top\mathbf X_t\,dt,$$

with $\mathbf B$ a vector of independent standard Brownian motions. Let $S_t = \sum_i X^i_t$ and $\mathbf Y_t = \mathbf X_t/S_t$ the patch distribution. Without space ($n = 1$) the stochastic growth rate is $\mu - \sigma^2/2$.

**Proposition.** If $\mathbf X_0 \ne 0$, then

$$d\mathbf Y_t = \big(\mathrm{diag}(\mathbf Y_t) - \mathbf Y_t\mathbf Y_t^\top\big)\Gamma^\top d\mathbf B_t + D^\top\mathbf Y_t\,dt + \big(\mathrm{diag}(\mathbf Y_t) - \mathbf Y_t\mathbf Y_t^\top\big)(\mu - \Sigma\mathbf Y_t)\,dt,$$

and $\mathbf Y_t$ converges in law to a random vector $\mathbf Y_\infty$ on the simplex, the empirical occupation measure of $\mathbf Y$ converging almost surely to its law.

**Theorem.** If $\mathbf X_0 \ne 0$, then almost surely

$$\chi := \lim_{t\to\infty}\frac1t\log S_t = \mu^\top\mathbb E[\mathbf Y_\infty] - \frac12\mathbb E\big[\mathbf Y_\infty^\top\Sigma\mathbf Y_\infty\big].$$

**Fast dispersal.** If $D = \delta Q$ with $Q$ an irreducible dispersal matrix with stationary distribution $\pi$ in the interior of the simplex, then as $\delta \to \infty$, $\mathbf Y_\infty(\delta) \to \pi$ in law and

$$\chi(\delta) \to \mu^\top\pi - \frac12\pi^\top\Sigma\pi.$$

Spreading over patches with imperfectly correlated noise lowers the variance penalty from $\sigma^2/2$ to $\pi^\top\Sigma\pi/2$, so dispersal can turn every locally declining population ($\mu_i - \sigma_{ii}/2 < 0$ for all $i$) into a persistent one.

## Expansion

By Itô's formula $d\log S_t = \big(\mu^\top\mathbf Y_t - \tfrac12\mathbf Y_t^\top\Sigma\mathbf Y_t\big)dt + \mathbf Y_t^\top\Gamma^\top d\mathbf B_t$, because dispersal conserves total abundance and the noise of $S$ is the $\mathbf Y$-weighted noise. The martingale term is $o(t)$, so $t^{-1}\log S_t$ is the time average of a function of $\mathbf Y$, and ergodicity of the patch-distribution diffusion (the dispersal term keeps it off the boundary) turns that average into the expectation under $\mathbf Y_\infty$. With fast irreducible dispersal, $\mathbf Y$ is pinned near the stationary law $\pi$ of $Q$.

## Sources

- Steven N. Evans, Peter L. Ralph, Sebastian J. Schreiber, Arnab Sen, "Stochastic population growth in spatially heterogeneous environments", arXiv (2011). Section 2 (model), Section 3 (Proposition 3.1, Theorem 3.2, Example 3.1), Section 4 (Proposition 4.1). <https://doi.org/10.48550/arXiv.1105.2280>. Published version: Journal of Mathematical Biology 66(3) (2013), 423–476, <https://doi.org/10.1007/s00285-012-0514-0>; locators above refer to the arXiv version.
