# The semicircle law is the unique zero of the rate function

For $\beta > 0$ and a probability measure $\mu$ on $\mathbb{R}$, $I_\beta(\mu) = 0$ if and only if
$\mu$ is the semicircle law $\sigma(dx) = \frac{1}{2\pi}\sqrt{4 - x^2}\,\mathbf{1}_{|x| \le 2}\,dx$.
In the sources, $I_\beta$ is strictly convex, so it has a unique minimiser,
characterised by the Euler–Lagrange equation
$\frac{x^2}{4} - \int \log|x - y|\,d\sigma(y) = \text{const}$ on its support; the semicircle law
solves it.

## Background

- [The Ben Arous–Guionnet rate function](ben-arous-guionnet-rate.md): the function minimised.

## Sources

- A. Guionnet, "Large deviations and stochastic calculus for large random matrices", *Probability
  Surveys* 1 (2004), 72–172, Theorem 3.1(1d, 1e).
- G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010 (numbering of the authors' pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), Lemma 2.6.2(d, e), equations (2.6.9)–(2.6.10).
