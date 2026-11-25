# Poly-Bernoulli polynomials

For a natural number $n$, an integer $k$ and a rational number
$x$, the poly-Bernoulli polynomial of degree $n$ and order $k$ at $x$ is the rational number

$$B_n^{(k)}(x) = \sum_{i=0}^{n} \binom{n}{i} B_i^{(k)} x^{n-i},$$

where $B_i^{(k)}$ are the poly-Bernoulli numbers.

These are the coefficients of the generating function
$\frac{\mathrm{Li}_k(1-e^{-t})}{1-e^{-t}} e^{xt} = \sum_{n \ge 0} B_n^{(k)}(x) \frac{t^n}{n!}$,
which is how the source defines them.

## Sources

- Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, definition of poly-Bernoulli polynomials before Corollary 3.
