# Beta-binomial distribution

For $n \in \mathbb{N}$, real $\alpha, \beta$ and $k \in \mathbb{N}$, the beta-binomial mass function is

$$\mathrm{BB}(n; \alpha, \beta)(k) = \frac{\binom{n}{k} \alpha^{(k)} \beta^{(n - k)}}{(\alpha + \beta)^{(n)}},$$

with the rising factorial $x^{(k)} = x(x+1) \cdots (x+k-1)$, $n - k$ read as $0$ when $k > n$, and a quotient with zero denominator read as $0$. It vanishes for $k > n$, since then $\binom{n}{k} = 0$, and for $\alpha, \beta > 0$ it is a probability mass function on $\{0, \dots, n\}$.

## Idea

Draw a success probability $\pi$ from the beta law with parameters $\alpha$ and $\beta$, then run $n$ independent trials with success probability $\pi$: the number of successes is beta-binomial. For positive integers $\alpha, \beta$ it is also the number of white balls drawn in $n$ draws from a Pólya urn that starts with $\alpha$ white and $\beta$ black balls and receives an extra ball of the drawn colour after each draw. The Chu–Vandermonde identity for rising factorials makes the masses sum to $1$. The mean is $n \pi$ with $\pi = \alpha / (\alpha + \beta)$, and the variance $n \pi (1 - \pi) \bigl(1 + (n - 1)/(\alpha + \beta + 1)\bigr)$ is at least the binomial one, and strictly larger when $n \ge 2$ (for $\alpha, \beta > 0$), because all trials share the same random $\pi$. This makes it a model for overdispersed proportions, such as methylation levels.

## Statements

- [Beta-binomial mass function](beta-binomial-pmf.md)
- [Beta-binomial masses sum to one](sum-beta-binomial-pmf.md): basic property: normalisation
- [Mean of the beta-binomial law](sum-mul-beta-binomial-pmf.md): basic property: the mean
- [Second factorial moment of the beta-binomial law](sum-mul-sub-one-beta-binomial-pmf.md): basic property: the second factorial moment
- [Variance of the beta-binomial law](variance-beta-binomial.md): basic property: the variance
- [Chu–Vandermonde identity for rising factorials](asc-pochhammer-eval-add-eq-sum.md): Chu–Vandermonde identity, used for normalisation
- [The binomial ratio is the beta-binomial mass](choose-mul-choose-div-choose-eq-beta-bin.md): binomial-ratio form of the mass
