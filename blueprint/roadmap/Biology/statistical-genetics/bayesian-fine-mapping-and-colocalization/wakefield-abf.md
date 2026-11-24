# Wakefield's approximate Bayes factor

For nonnegative reals $V$ and $W$ and a real number $b$, Wakefield's approximate Bayes factor is

$$\mathrm{ABF}(V, W, b) = \frac{\varphi_{V+W}(b)}{\varphi_V(b)},$$

where $\varphi_v(b) = (2\pi v)^{-1/2} e^{-b^2/(2v)}$, with the conventions $0^{-1} = 0$ and $x/0 = 0$; for $v > 0$ it is the density at $b$ of the centred normal distribution with variance $v$. Thus $\varphi_0 = 0$, which is not a density of the point mass at $0$, and $\mathrm{ABF}(0, W, b) = 0$.

For $V > 0$, $b$ is read as an effect estimate with sampling variance $V$: the numerator is its density under the alternative, where the true effect has an $N(0, W)$ prior, and the denominator its density under the null of no effect. Large values favour association; Wakefield (2009) reports the reciprocal.

## Sources

- J. Wakefield, *Bayes factors for genome-wide association studies: comparison with P-values*, Genet. Epidemiol. 33 (2009), 79–86.
