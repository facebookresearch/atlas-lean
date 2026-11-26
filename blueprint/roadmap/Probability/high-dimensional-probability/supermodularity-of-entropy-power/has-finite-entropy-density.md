# Real random variable with a finite-entropy density

Let $(\Omega, P)$ be a measure space, not necessarily a probability space, and $X : \Omega \to \mathbb{R}$ a function. Let $g$ be the Radon–Nikodym derivative of the image measure of $P$ under $X$ with respect to Lebesgue measure, a function with values in $[0, \infty]$, and let $f = \tilde g$ be its real version, with $\tilde\infty = 0$. Then $X$ has a density of finite entropy if

- $X$ has a density with respect to Lebesgue measure: $X$ is almost everywhere measurable, its image measure is absolutely continuous with respect to Lebesgue measure, and that image measure is the measure with density $g$; and
- the real function $x \mapsto f(x) \log f(x)$ is Lebesgue integrable on $\mathbb{R}$, with $0 \log 0 = 0$.

The integrand uses the real version $f$, so a set where $g = \infty$ contributes nothing: for $P$ equal to Lebesgue measure with constant density $\infty$ and $X$ the identity, the first condition holds, $g = \infty$ almost everywhere and the integrand is zero. When $P$ is a probability measure, $g$ is finite almost everywhere and $f$ is the usual probability density of $X$.
