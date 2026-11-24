# The Ben Arous–Guionnet rate function

For real $\beta$ and a probability measure $\mu$ on $\mathbb{R}$,

$$I_\beta(\mu) = \Bigl(\frac{\beta}{2}\Bigr)^+ \iint g \, d\mu\, d\mu - \Bigl(\frac{\beta}{8} + \frac{\beta}{2}\log 2\Bigr)^+ \in [0, \infty],$$

with the nonnegative [logarithmic-energy kernel](log-energy-kernel.md) $g$: the double integral is
taken in $[0, \infty]$ (with $0 \cdot \infty = 0$), both coefficients are replaced by their positive parts
$c^+ = \max(c, 0)$, and the subtraction is truncated at $0$. For $\beta > 0$ the coefficients are
$\frac{\beta}{2}$ and $\frac{\beta}{8} + \frac{\beta}{2}\log 2$; for $\beta \le 0$ both vanish, so $I_\beta = 0$.

For $\beta > 0$ and $\mu$ with finite second moment this is the source's formula

$$I_\beta(\mu) = \frac{\beta}{4} \int x^2 \, d\mu(x) - \frac{\beta}{2} \iint \log |x - y| \, d\mu(x)\,d\mu(y) - \frac{3\beta}{8},$$

because then $\frac{\beta}{2}\iint f\,d\mu\,d\mu = \frac{\beta}{4}\int x^2\,d\mu - \frac{\beta}{2}\iint \log|x-y|\,d\mu\,d\mu$
for Guionnet's kernel $f = g + \frac12 - \log 2$, and
$\frac{\beta}{2}(\frac{1}{2} - \log 2) - \frac{3\beta}{8} = -\frac{\beta}{8} - \frac{\beta}{2}\log 2$; the truncation
loses nothing, since this value is nonnegative. Without a finite second moment the two separate
integrals can both be infinite, leaving $\infty - \infty$ (for instance for a mixture of the uniform
laws on $[e^n, e^n + 1]$ with weights proportional to $1/n^2$), while the combined integral of $g$ is
always defined. For $\beta > 0$, $I_\beta(\mu) = \infty$ when $\mu$ has an atom (the diagonal, where
$g = \infty$, then has positive mass) or an infinite second moment. At the semicircle law,
$\int x^2\,d\sigma = 1$ and $\iint \log|x-y|\,d\sigma\,d\sigma = -\frac{1}{4}$, so
$I_\beta(\sigma) = \frac{\beta}{4} + \frac{\beta}{8} - \frac{3\beta}{8} = 0$.

## Sources

- A. Guionnet, "Large deviations and stochastic calculus for large random matrices", *Probability
  Surveys* 1 (2004), 72–172, Theorem 3.1(1).
- G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010 (numbering of the authors' pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), the function $I^V_\beta$ of Theorem 2.6.1 with $V(x) = \beta x^2/4$.
