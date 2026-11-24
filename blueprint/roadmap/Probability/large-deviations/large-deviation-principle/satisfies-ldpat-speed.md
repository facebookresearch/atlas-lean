# Large deviation principle at speed $a_N$

Let $X$ be a topological space whose open sets are measurable, let $(a_N)$ be real numbers with
$a_N \to \infty$, let $\mu_N$ be measures on $X$ and $I : X \to [0, \infty]$. The sequence
$(\mu_N)$ satisfies the large deviation principle at speed $a_N$ with rate function $I$ if $I$ is
lower semicontinuous and, in $[-\infty, \infty]$,

$$\liminf_{N \to \infty} \frac{1}{a_N} \log \mu_N(U) \ge -\inf_U I \ \ (U \text{ open}), \qquad \limsup_{N \to \infty} \frac{1}{a_N} \log \mu_N(F) \le -\inf_F I \ \ (F \text{ closed}).$$

The conditions mirror those of the [large deviation principle](satisfies-ldp.md) at speed $N$,
which is the case $a_N = N$ ([speed $n$ is the usual principle](satisfies-ldpat-speed-nat-cast-iff.md)).
Other speeds occur for random matrices, where the empirical spectral measure of an $N \times N$
Gaussian matrix deviates at speed $N^2$
([Ben Arous–Guionnet](../ben-arous-guionnet-large-deviations/ben-arous-guionnet-ldp.md)), and for
moderate deviations.

## Sources

- A. Guionnet, "Large deviations and stochastic calculus for large random matrices", *Probability
  Surveys* 1 (2004), 72–172, arXiv:math/0409277, Definition 2.1.
