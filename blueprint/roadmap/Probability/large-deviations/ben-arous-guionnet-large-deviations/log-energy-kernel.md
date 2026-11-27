# Logarithmic-energy kernel

The kernel

$$g(x, y) = \log \frac{1}{|x - y|} + \frac{x^2 + y^2}{4} - \Bigl(\frac{1}{2} - \log 2\Bigr)
\quad (x \ne y), \qquad g(x, x) = +\infty,$$

with values in $[0, \infty]$. It is nonnegative: $\frac{x^2 + y^2}{4} \ge \frac{(x - y)^2}{8}$, and
$d \mapsto -\log d + d^2/8$ has minimum $\frac{1}{2} - \log 2$ at $d = 2$. It is the kernel
$f(x,y) = \log|x-y|^{-1} + \frac{x^2+y^2}{4}$ of Guionnet's proof, shifted to be nonnegative so that
its double integral is a well-defined element of $[0, \infty]$ for every probability measure.

## Sources

- A. Guionnet, "Large deviations and stochastic calculus for large random matrices", *Probability
  Surveys* 1 (2004), 72–172, proof of Theorem 3.1 (the function $f$).
